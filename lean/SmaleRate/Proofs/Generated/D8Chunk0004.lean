/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0100; no trusted numerical premise.
theorem cover8_leaf0100_exp_radius : (62380249926744531/62500000000000000 : ℝ) ≤ Real.exp ((-2011/131072 : ℝ)/8) ∧ Real.exp ((-2011/131072 : ℝ)/8) ≤ (998083998827912497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2011/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0100_exp_lower : (920114223639690153/1000000000000000000 : ℝ) ≤ Real.exp ((-1332119368251/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332119368251/2000000000000 : ℝ)/8) ≤ (460057111819845077/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332119368251/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0100_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915395431/1000000000000 : ℝ) ≤ 4*Real.exp (1005/8192 : ℝ)*Real.exp (-mu (radius 8 (2011/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915395431/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2011/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0100_exp_radius
  have hrNumeric : (123096798421/125000000000 : ℝ) ≤ Real.exp (-2011/131072 : ℝ) ∧ Real.exp (-2011/131072 : ℝ) ≤ (984774387369/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123096798421/125000000000 : ℝ) ≤ (radius 8 (2011/16384 : ℝ)) ∧ (radius 8 (2011/16384 : ℝ)) ≤ (984774387369/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2011/16384 : ℝ)) (123096798421/125000000000 : ℝ) (984774387369/1000000000000 : ℝ) (86918648721/500000000000 : ℝ) (21729662181/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2011/16384 : ℝ)) (123096798421/125000000000 : ℝ) (984774387369/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123096798421/125000000000 : ℝ) (984774387369/1000000000000 : ℝ) (248096798421/250000000000 : ℝ) (198477438737/200000000000 : ℝ) (62022374597/62500000000 : ℝ) (496178996777/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 1 (248096798421/250000000000 : ℝ) (198477438737/200000000000 : ℝ) (62022374597/62500000000 : ℝ) (496178996777/500000000000 : ℝ) (496186296809/500000000000 : ℝ) (49618629681/50000000000 : ℝ) (99237259351/100000000000 : ℝ) (992372593513/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 2 (496186296809/500000000000 : ℝ) (49618629681/50000000000 : ℝ) (99237259351/100000000000 : ℝ) (992372593513/1000000000000 : ℝ) (248093148391/250000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 3 (248093148391/250000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 4 (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 5 (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 6 (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2011/16384 : ℝ)) 7 (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2011/16384 : ℝ))) (86918648721/500000000000 : ℝ) (21729662181/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86918648721/500000000000 : ℝ) (21729662181/125000000000 : ℝ) (586918648721/1000000000000 : ℝ) (146729662181/250000000000 : ℝ) (104234500479/250000000000 : ℝ) (104234500481/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 1 (586918648721/1000000000000 : ℝ) (146729662181/250000000000 : ℝ) (104234500479/250000000000 : ℝ) (104234500481/250000000000 : ℝ) (250964162659/500000000000 : ℝ) (125482081331/250000000000 : ℝ) (494680390439/1000000000000 : ℝ) (247340195223/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 2 (250964162659/500000000000 : ℝ) (125482081331/250000000000 : ℝ) (494680390439/1000000000000 : ℝ) (247340195223/500000000000 : ℝ) (249152178939/500000000000 : ℝ) (99660871577/200000000000 : ℝ) (249145589937/500000000000 : ℝ) (498291179881/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 3 (249152178939/500000000000 : ℝ) (99660871577/200000000000 : ℝ) (249145589937/500000000000 : ℝ) (498291179881/1000000000000 : ℝ) (124574442219/250000000000 : ℝ) (498297768883/1000000000000 : ℝ) (3892951319/7812500000 : ℝ) (12457444221/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 4 (124574442219/250000000000 : ℝ) (498297768883/1000000000000 : ℝ) (3892951319/7812500000 : ℝ) (12457444221/25000000000 : ℝ) (249148884427/500000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 5 (249148884427/500000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 6 (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2011/16384 : ℝ))) 7 (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2011/16384 : ℝ)) hmem 8 (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2011/16384 : ℝ))) hcmem 8 (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2011/16384 : ℝ)) (992372593563/1000000000000 : ℝ) (992372593567/1000000000000 : ℝ) (498297768853/1000000000000 : ℝ) (249148884431/500000000000 : ℝ) (788740348169/1000000000000 : ℝ) (197185087047/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0100_exp_lower
  have heNumeric : (2054915395431/1000000000000 : ℝ)/4 ≤ Real.exp (-1332119368251/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915395431/1000000000000 : ℝ)/4 ≤ Real.exp ((1005/8192 : ℝ)-(197185087047/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1005/8192 : ℝ) (2011/16384 : ℝ) (197185087047/250000000000 : ℝ) (2054915395431/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0101; no trusted numerical premise.
theorem cover8_leaf0101_exp_radius : (499041523490645537/500000000000000000 : ℝ) ≤ Real.exp ((-503/32768 : ℝ)/8) ∧ Real.exp ((-503/32768 : ℝ)/8) ≤ (39923321879251643/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-503/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0101_exp_lower : (460057017398667627/500000000000000000 : ℝ) ≤ Real.exp ((-2664245304117/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664245304117/4000000000000 : ℝ)/8) ≤ (184022806959467051/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664245304117/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0101_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912021461/1000000000000 : ℝ) ≤ 4*Real.exp (2011/16384 : ℝ)*Real.exp (-mu (radius 8 (503/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912021461/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (503/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0101_exp_radius
  have hrNumeric : (246191718541/250000000000 : ℝ) ≤ Real.exp (-503/32768 : ℝ) ∧ Real.exp (-503/32768 : ℝ) ≤ (196953374833/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246191718541/250000000000 : ℝ) ≤ (radius 8 (503/4096 : ℝ)) ∧ (radius 8 (503/4096 : ℝ)) ≤ (196953374833/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (503/4096 : ℝ)) (246191718541/250000000000 : ℝ) (196953374833/200000000000 : ℝ) (17387985377/100000000000 : ℝ) (173879853777/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (503/4096 : ℝ)) (246191718541/250000000000 : ℝ) (196953374833/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (503/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246191718541/250000000000 : ℝ) (196953374833/200000000000 : ℝ) (496191718541/500000000000 : ℝ) (992383437083/1000000000000 : ℝ) (496177104007/500000000000 : ℝ) (198470841603/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (503/4096 : ℝ)) 1 (496191718541/500000000000 : ℝ) (992383437083/1000000000000 : ℝ) (496177104007/500000000000 : ℝ) (198470841603/200000000000 : ℝ) (248092205637/250000000000 : ℝ) (992368822549/1000000000000 : ℝ) (24809220561/25000000000 : ℝ) (496184411221/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (503/4096 : ℝ)) 2 (248092205637/250000000000 : ℝ) (992368822549/1000000000000 : ℝ) (24809220561/25000000000 : ℝ) (496184411221/500000000000 : ℝ) (496184411247/500000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (503/4096 : ℝ)) 3 (496184411247/500000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (503/4096 : ℝ)) 4 (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (503/4096 : ℝ)) 5 (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (503/4096 : ℝ)) 6 (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (503/4096 : ℝ)) 7 (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (503/4096 : ℝ))) (17387985377/100000000000 : ℝ) (173879853777/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17387985377/100000000000 : ℝ) (173879853777/1000000000000 : ℝ) (117387985377/200000000000 : ℝ) (586939926889/1000000000000 : ℝ) (416989033153/1000000000000 : ℝ) (208494516581/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 1 (117387985377/200000000000 : ℝ) (586939926889/1000000000000 : ℝ) (416989033153/1000000000000 : ℝ) (208494516581/500000000000 : ℝ) (501964480019/1000000000000 : ℝ) (250982240013/500000000000 : ℝ) (247359815163/500000000000 : ℝ) (247359815167/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 2 (501964480019/1000000000000 : ℝ) (250982240013/500000000000 : ℝ) (247359815163/500000000000 : ℝ) (247359815167/500000000000 : ℝ) (124585513793/250000000000 : ℝ) (24917102759/50000000000 : ℝ) (498328889381/1000000000000 : ℝ) (498328889389/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 3 (124585513793/250000000000 : ℝ) (24917102759/50000000000 : ℝ) (498328889381/1000000000000 : ℝ) (498328889389/1000000000000 : ℝ) (124583868069/250000000000 : ℝ) (99667094457/200000000000 : ℝ) (498335472233/1000000000000 : ℝ) (249167736121/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 4 (124583868069/250000000000 : ℝ) (99667094457/200000000000 : ℝ) (498335472233/1000000000000 : ℝ) (249167736121/500000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 5 (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 6 (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (503/4096 : ℝ))) 7 (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (503/4096 : ℝ)) hmem 8 (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (503/4096 : ℝ))) hcmem 8 (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (503/4096 : ℝ)) (992368822493/1000000000000 : ℝ) (31011525703/31250000000 : ℝ) (249167736127/500000000000 : ℝ) (62291934033/125000000000 : ℝ) (788803025229/1000000000000 : ℝ) (24650094539/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0101_exp_lower
  have heNumeric : (2054912021461/1000000000000 : ℝ)/4 ≤ Real.exp (-2664245304117/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912021461/1000000000000 : ℝ)/4 ≤ Real.exp ((2011/16384 : ℝ)-(24650094539/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2011/16384 : ℝ) (503/4096 : ℝ) (24650094539/31250000000 : ℝ) (2054912021461/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0102; no trusted numerical premise.
theorem cover8_leaf0102_exp_radius : (998082095135577403/1000000000000000000 : ℝ) ≤ Real.exp ((-2013/131072 : ℝ)/8) ∧ Real.exp ((-2013/131072 : ℝ)/8) ≤ (249520523783894351/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2013/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0102_exp_lower : (184022769678595153/200000000000000000 : ℝ) ≤ Real.exp ((-41628934171/62500000000 : ℝ)/8) ∧ Real.exp ((-41628934171/62500000000 : ℝ)/8) ≤ (460056924196487883/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41628934171/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0102_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908691053/1000000000000 : ℝ) ≤ 4*Real.exp (503/4096 : ℝ)*Real.exp (-mu (radius 8 (2013/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908691053/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2013/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0102_exp_radius
  have hrNumeric : (492379680509/500000000000 : ℝ) ≤ Real.exp (-2013/131072 : ℝ) ∧ Real.exp (-2013/131072 : ℝ) ≤ (984759361019/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492379680509/500000000000 : ℝ) ≤ (radius 8 (2013/16384 : ℝ)) ∧ (radius 8 (2013/16384 : ℝ)) ≤ (984759361019/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2013/16384 : ℝ)) (492379680509/500000000000 : ℝ) (984759361019/1000000000000 : ℝ) (173922399033/1000000000000 : ℝ) (173922399039/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2013/16384 : ℝ)) (492379680509/500000000000 : ℝ) (984759361019/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492379680509/500000000000 : ℝ) (984759361019/1000000000000 : ℝ) (992379680509/1000000000000 : ℝ) (99237968051/100000000000 : ℝ) (99235042249/100000000000 : ℝ) (248087605623/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 1 (992379680509/1000000000000 : ℝ) (99237968051/100000000000 : ℝ) (99235042249/100000000000 : ℝ) (248087605623/250000000000 : ℝ) (992365051499/1000000000000 : ℝ) (992365051501/1000000000000 : ℝ) (992365051391/1000000000000 : ℝ) (496182525697/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 2 (992365051499/1000000000000 : ℝ) (992365051501/1000000000000 : ℝ) (992365051391/1000000000000 : ℝ) (496182525697/500000000000 : ℝ) (198473010289/200000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 3 (198473010289/200000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 4 (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 5 (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 6 (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2013/16384 : ℝ)) 7 (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2013/16384 : ℝ))) (173922399033/1000000000000 : ℝ) (173922399039/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173922399033/1000000000000 : ℝ) (173922399039/1000000000000 : ℝ) (146740299879/250000000000 : ℝ) (3668507497/6250000000 : ℝ) (417040044879/1000000000000 : ℝ) (417040044887/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 1 (146740299879/250000000000 : ℝ) (3668507497/6250000000 : ℝ) (417040044879/1000000000000 : ℝ) (417040044887/1000000000000 : ℝ) (502000622197/1000000000000 : ℝ) (125500155551/250000000000 : ℝ) (494758855391/1000000000000 : ℝ) (494758855399/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 2 (502000622197/1000000000000 : ℝ) (125500155551/250000000000 : ℝ) (494758855391/1000000000000 : ℝ) (494758855399/1000000000000 : ℝ) (249189869397/500000000000 : ℝ) (249189869401/500000000000 : ℝ) (498366585199/1000000000000 : ℝ) (62295823151/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 3 (249189869397/500000000000 : ℝ) (249189869401/500000000000 : ℝ) (498366585199/1000000000000 : ℝ) (62295823151/125000000000 : ℝ) (124593290499/250000000000 : ℝ) (99674632401/200000000000 : ℝ) (498373161953/1000000000000 : ℝ) (249186580981/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 4 (124593290499/250000000000 : ℝ) (99674632401/200000000000 : ℝ) (498373161953/1000000000000 : ℝ) (249186580981/500000000000 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 5 (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 6 (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2013/16384 : ℝ))) 7 (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2013/16384 : ℝ)) hmem 8 (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2013/16384 : ℝ))) hcmem 8 (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2013/16384 : ℝ)) (248091262861/250000000000 : ℝ) (124045631431/125000000000 : ℝ) (249186580987/500000000000 : ℝ) (486692541/976562500 : ℝ) (788865681091/1000000000000 : ℝ) (788865681111/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0102_exp_lower
  have heNumeric : (2054908691053/1000000000000 : ℝ)/4 ≤ Real.exp (-41628934171/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908691053/1000000000000 : ℝ)/4 ≤ Real.exp ((503/4096 : ℝ)-(788865681111/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (503/4096 : ℝ) (2013/16384 : ℝ) (788865681111/1000000000000 : ℝ) (2054908691053/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0103; no trusted numerical premise.
theorem cover8_leaf0103_exp_radius : (499040571645385741/500000000000000000 : ℝ) ≤ Real.exp ((-1007/65536 : ℝ)/8) ∧ Real.exp ((-1007/65536 : ℝ)/8) ≤ (998081143290771483/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1007/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0103_exp_lower : (920113664423504821/1000000000000000000 : ℝ) ≤ Real.exp ((-2664258185091/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664258185091/4000000000000 : ℝ)/8) ≤ (460056832211752411/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664258185091/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0103_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452702077/500000000000 : ℝ) ≤ 4*Real.exp (2013/16384 : ℝ)*Real.exp (-mu (radius 8 (1007/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452702077/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1007/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0103_exp_radius
  have hrNumeric : (984751847929/1000000000000 : ℝ) ≤ Real.exp (-1007/65536 : ℝ) ∧ Real.exp (-1007/65536 : ℝ) ≤ (98475184793/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984751847929/1000000000000 : ℝ) ≤ (radius 8 (1007/8192 : ℝ)) ∧ (radius 8 (1007/8192 : ℝ)) ≤ (98475184793/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1007/8192 : ℝ)) (984751847929/1000000000000 : ℝ) (98475184793/100000000000 : ℝ) (173964933243/1000000000000 : ℝ) (695859733/4000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1007/8192 : ℝ)) (984751847929/1000000000000 : ℝ) (98475184793/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984751847929/1000000000000 : ℝ) (98475184793/100000000000 : ℝ) (248093980991/250000000000 : ℝ) (198475184793/200000000000 : ℝ) (992346636981/1000000000000 : ℝ) (992346636983/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 1 (248093980991/250000000000 : ℝ) (198475184793/200000000000 : ℝ) (992346636981/1000000000000 : ℝ) (992346636983/1000000000000 : ℝ) (124045160059/125000000000 : ℝ) (496180640237/500000000000 : ℝ) (248090320091/250000000000 : ℝ) (496180640183/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 2 (124045160059/125000000000 : ℝ) (496180640237/500000000000 : ℝ) (248090320091/250000000000 : ℝ) (496180640183/500000000000 : ℝ) (496180640209/500000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 3 (496180640209/500000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 4 (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 5 (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 6 (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1007/8192 : ℝ)) 7 (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1007/8192 : ℝ))) (173964933243/1000000000000 : ℝ) (695859733/4000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173964933243/1000000000000 : ℝ) (695859733/4000000000 : ℝ) (586982466621/1000000000000 : ℝ) (4695859733/8000000000 : ℝ) (104272759279/250000000000 : ℝ) (3336728297/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 1 (586982466621/1000000000000 : ℝ) (4695859733/8000000000 : ℝ) (104272759279/250000000000 : ℝ) (3336728297/8000000000 : ℝ) (125509187967/250000000000 : ℝ) (803258803/1600000000 : ℝ) (9895961313/20000000000 : ℝ) (247399032829/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 2 (125509187967/250000000000 : ℝ) (803258803/1600000000 : ℝ) (9895961313/20000000000 : ℝ) (247399032829/500000000000 : ℝ) (498417408759/1000000000000 : ℝ) (498417408767/1000000000000 : ℝ) (249202133673/500000000000 : ℝ) (99680853471/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 3 (498417408759/1000000000000 : ℝ) (498417408767/1000000000000 : ℝ) (249202133673/500000000000 : ℝ) (99680853471/200000000000 : ℝ) (124602709513/250000000000 : ℝ) (498410838061/1000000000000 : ℝ) (498410838009/1000000000000 : ℝ) (249205419009/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 4 (124602709513/250000000000 : ℝ) (498410838061/1000000000000 : ℝ) (498410838009/1000000000000 : ℝ) (249205419009/500000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 5 (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 6 (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1007/8192 : ℝ))) 7 (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1007/8192 : ℝ)) hmem 8 (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1007/8192 : ℝ))) hcmem 8 (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1007/8192 : ℝ)) (992361280417/1000000000000 : ℝ) (49618064021/50000000000 : ℝ) (49841083803/100000000000 : ℝ) (12460270951/25000000000 : ℝ) (157785663157/200000000000 : ℝ) (197232078951/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0103_exp_lower
  have heNumeric : (1027452702077/500000000000 : ℝ)/4 ≤ Real.exp (-2664258185091/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452702077/500000000000 : ℝ)/4 ≤ Real.exp ((2013/16384 : ℝ)-(197232078951/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2013/16384 : ℝ) (1007/8192 : ℝ) (197232078951/250000000000 : ℝ) (1027452702077/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0104; no trusted numerical premise.
theorem cover8_leaf0104_exp_radius : (998080191446873311/1000000000000000000 : ℝ) ≤ Real.exp ((-2015/131072 : ℝ)/8) ∧ Real.exp ((-2015/131072 : ℝ)/8) ≤ (31190005982714791/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2015/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0104_exp_lower : (920113482886620677/1000000000000000000 : ℝ) ≤ Real.exp ((-1332132249319/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332132249319/2000000000000 : ℝ)/8) ≤ (460056741443310339/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332132249319/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0104_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902160721/1000000000000 : ℝ) ≤ 4*Real.exp (1007/8192 : ℝ)*Real.exp (-mu (radius 8 (2015/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902160721/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2015/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0104_exp_radius
  have hrNumeric : (984744334897/1000000000000 : ℝ) ≤ Real.exp (-2015/131072 : ℝ) ∧ Real.exp (-2015/131072 : ℝ) ≤ (492372167449/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984744334897/1000000000000 : ℝ) ≤ (radius 8 (2015/16384 : ℝ)) ∧ (radius 8 (2015/16384 : ℝ)) ≤ (492372167449/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2015/16384 : ℝ)) (984744334897/1000000000000 : ℝ) (492372167449/500000000000 : ℝ) (17400745641/100000000000 : ℝ) (5437733013/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2015/16384 : ℝ)) (984744334897/1000000000000 : ℝ) (492372167449/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984744334897/1000000000000 : ℝ) (492372167449/500000000000 : ℝ) (124046520931/125000000000 : ℝ) (992372167449/1000000000000 : ℝ) (496171425743/500000000000 : ℝ) (31010714109/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 1 (124046520931/125000000000 : ℝ) (992372167449/1000000000000 : ℝ) (496171425743/500000000000 : ℝ) (31010714109/31250000000 : ℝ) (992357509467/1000000000000 : ℝ) (992357509469/1000000000000 : ℝ) (496178754679/500000000000 : ℝ) (992357509361/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 2 (992357509467/1000000000000 : ℝ) (992357509469/1000000000000 : ℝ) (496178754679/500000000000 : ℝ) (992357509361/1000000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 3 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 4 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 5 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 6 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2015/16384 : ℝ)) 7 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2015/16384 : ℝ))) (17400745641/100000000000 : ℝ) (5437733013/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17400745641/100000000000 : ℝ) (5437733013/31250000000 : ℝ) (117400745641/200000000000 : ℝ) (36687733013/62500000000 : ℝ) (417142009883/1000000000000 : ℝ) (104285502473/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 1 (117400745641/200000000000 : ℝ) (36687733013/62500000000 : ℝ) (417142009883/1000000000000 : ℝ) (104285502473/250000000000 : ℝ) (125518217261/250000000000 : ℝ) (10041457381/20000000000 : ℝ) (494837261119/1000000000000 : ℝ) (494837261127/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 2 (125518217261/250000000000 : ℝ) (10041457381/20000000000 : ℝ) (494837261119/1000000000000 : ℝ) (494837261127/1000000000000 : ℝ) (498455065081/1000000000000 : ℝ) (498455065089/1000000000000 : ℝ) (99688387167/200000000000 : ℝ) (498441935843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 3 (498455065081/1000000000000 : ℝ) (498455065089/1000000000000 : ℝ) (99688387167/200000000000 : ℝ) (498441935843/1000000000000 : ℝ) (249224250229/500000000000 : ℝ) (249224250233/500000000000 : ℝ) (249224250207/500000000000 : ℝ) (498448500423/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 4 (249224250229/500000000000 : ℝ) (249224250233/500000000000 : ℝ) (249224250207/500000000000 : ℝ) (498448500423/1000000000000 : ℝ) (124612125109/250000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 5 (124612125109/250000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 6 (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2015/16384 : ℝ))) 7 (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2015/16384 : ℝ)) hmem 8 (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2015/16384 : ℝ))) hcmem 8 (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2015/16384 : ℝ)) (248089377353/250000000000 : ℝ) (198471501883/200000000000 : ℝ) (99689700087/200000000000 : ℝ) (99689700089/200000000000 : ℝ) (49311933083/62500000000 : ℝ) (788990929347/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0104_exp_lower
  have heNumeric : (2054902160721/1000000000000 : ℝ)/4 ≤ Real.exp (-1332132249319/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902160721/1000000000000 : ℝ)/4 ≤ Real.exp ((1007/8192 : ℝ)-(788990929347/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1007/8192 : ℝ) (2015/16384 : ℝ) (788990929347/1000000000000 : ℝ) (2054902160721/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0105; no trusted numerical premise.
theorem cover8_leaf0105_exp_radius : (998079715525264631/1000000000000000000 : ℝ) ≤ Real.exp ((-4031/262144 : ℝ)/8) ∧ Real.exp ((-4031/262144 : ℝ)/8) ≤ (124759964440658079/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4031/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0105_exp_lower : (920116902990936101/1000000000000000000 : ℝ) ≤ Real.exp ((-2664145553381/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664145553381/4000000000000 : ℝ)/8) ≤ (460058451495468051/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664145553381/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0105_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027481633423/500000000000 : ℝ) ≤ 4*Real.exp (2015/16384 : ℝ)*Real.exp (-mu (radius 8 (4031/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027481633423/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4031/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0105_exp_radius
  have hrNumeric : (984740578403/1000000000000 : ℝ) ≤ Real.exp (-4031/262144 : ℝ) ∧ Real.exp (-4031/262144 : ℝ) ≤ (246185144601/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984740578403/1000000000000 : ℝ) ≤ (radius 8 (4031/32768 : ℝ)) ∧ (radius 8 (4031/32768 : ℝ)) ≤ (246185144601/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4031/32768 : ℝ)) (984740578403/1000000000000 : ℝ) (246185144601/250000000000 : ℝ) (3480574277/20000000000 : ℝ) (174028713857/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4031/32768 : ℝ)) (984740578403/1000000000000 : ℝ) (246185144601/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984740578403/1000000000000 : ℝ) (246185144601/250000000000 : ℝ) (992370289201/1000000000000 : ℝ) (496185144601/500000000000 : ℝ) (198468191749/200000000000 : ℝ) (496170479373/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 1 (992370289201/1000000000000 : ℝ) (496185144601/500000000000 : ℝ) (198468191749/200000000000 : ℝ) (496170479373/500000000000 : ℝ) (992355623973/1000000000000 : ℝ) (496177811987/500000000000 : ℝ) (124044452983/125000000000 : ℝ) (496177811933/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 2 (992355623973/1000000000000 : ℝ) (496177811987/500000000000 : ℝ) (124044452983/125000000000 : ℝ) (496177811933/500000000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 3 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 4 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 5 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 6 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4031/32768 : ℝ)) 7 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4031/32768 : ℝ))) (3480574277/20000000000 : ℝ) (174028713857/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3480574277/20000000000 : ℝ) (174028713857/1000000000000 : ℝ) (23480574277/40000000000 : ℝ) (587014356929/1000000000000 : ℝ) (83433497793/200000000000 : ℝ) (16686699559/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 1 (23480574277/40000000000 : ℝ) (587014356929/1000000000000 : ℝ) (83433497793/200000000000 : ℝ) (16686699559/40000000000 : ℝ) (100418184589/200000000000 : ℝ) (62761365369/125000000000 : ℝ) (247428426653/500000000000 : ℝ) (98971370663/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 2 (100418184589/200000000000 : ℝ) (62761365369/125000000000 : ℝ) (247428426653/500000000000 : ℝ) (98971370663/200000000000 : ℝ) (797558221/1600000000 : ℝ) (249236944067/500000000000 : ℝ) (498460764957/1000000000000 : ℝ) (249230382483/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 3 (797558221/1600000000 : ℝ) (249236944067/500000000000 : ℝ) (498460764957/1000000000000 : ℝ) (249230382483/500000000000 : ℝ) (498467326541/1000000000000 : ℝ) (9969346531/20000000000 : ℝ) (498467326497/1000000000000 : ℝ) (498467326507/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 4 (498467326541/1000000000000 : ℝ) (9969346531/20000000000 : ℝ) (498467326497/1000000000000 : ℝ) (498467326507/1000000000000 : ℝ) (498467326519/1000000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 5 (498467326519/1000000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 6 (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4031/32768 : ℝ))) 7 (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4031/32768 : ℝ)) hmem 8 (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4031/32768 : ℝ))) hcmem 8 (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4031/32768 : ℝ)) (496177811959/500000000000 : ℝ) (12404445299/12500000000 : ℝ) (249233663259/500000000000 : ℝ) (498467326529/1000000000000 : ℝ) (789022228169/1000000000000 : ℝ) (789022228189/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0105_exp_lower
  have heNumeric : (1027481633423/500000000000 : ℝ)/4 ≤ Real.exp (-2664145553381/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027481633423/500000000000 : ℝ)/4 ≤ Real.exp ((2015/16384 : ℝ)-(789022228189/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2015/16384 : ℝ) (4031/32768 : ℝ) (789022228189/1000000000000 : ℝ) (1027481633423/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0106; no trusted numerical premise.
theorem cover8_leaf0106_exp_radius : (998079239603882889/1000000000000000000 : ℝ) ≤ Real.exp ((-63/4096 : ℝ)/8) ∧ Real.exp ((-63/4096 : ℝ)/8) ≤ (99807923960388289/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-63/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0106_exp_lower : (18402336274829109/20000000000000000 : ℝ) ≤ Real.exp ((-5328297314633/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328297314633/8000000000000 : ℝ)/8) ≤ (920116813741455451/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328297314633/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0106_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513740418057/250000000000 : ℝ) ≤ 4*Real.exp (4031/32768 : ℝ)*Real.exp (-mu (radius 8 (63/512 : ℝ))) ∧ (20549/10000 : ℝ) < (513740418057/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (63/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0106_exp_radius
  have hrNumeric : (984736821923/1000000000000 : ℝ) ≤ Real.exp (-63/4096 : ℝ) ∧ Real.exp (-63/4096 : ℝ) ≤ (246184205481/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984736821923/1000000000000 : ℝ) ≤ (radius 8 (63/512 : ℝ)) ∧ (radius 8 (63/512 : ℝ)) ≤ (246184205481/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (63/512 : ℝ)) (984736821923/1000000000000 : ℝ) (246184205481/250000000000 : ℝ) (87024984267/500000000000 : ℝ) (174049968541/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (63/512 : ℝ)) (984736821923/1000000000000 : ℝ) (246184205481/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (63/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984736821923/1000000000000 : ℝ) (246184205481/250000000000 : ℝ) (992368410961/1000000000000 : ℝ) (496184205481/500000000000 : ℝ) (496169533003/500000000000 : ℝ) (124042383251/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (63/512 : ℝ)) 1 (992368410961/1000000000000 : ℝ) (496184205481/500000000000 : ℝ) (496169533003/500000000000 : ℝ) (124042383251/125000000000 : ℝ) (992353738483/1000000000000 : ℝ) (198470747697/200000000000 : ℝ) (7938829907/8000000000 : ℝ) (992353738377/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (63/512 : ℝ)) 2 (992353738483/1000000000000 : ℝ) (198470747697/200000000000 : ℝ) (7938829907/8000000000 : ℝ) (992353738377/1000000000000 : ℝ) (992353738429/1000000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (63/512 : ℝ)) 3 (992353738429/1000000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (63/512 : ℝ)) 4 (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (63/512 : ℝ)) 5 (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (63/512 : ℝ)) 6 (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (63/512 : ℝ)) 7 (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (63/512 : ℝ))) (87024984267/500000000000 : ℝ) (174049968541/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87024984267/500000000000 : ℝ) (174049968541/1000000000000 : ℝ) (587024984267/1000000000000 : ℝ) (587024984271/1000000000000 : ℝ) (104298240797/250000000000 : ℝ) (417192963197/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 1 (587024984267/1000000000000 : ℝ) (587024984271/1000000000000 : ℝ) (104298240797/250000000000 : ℝ) (417192963197/1000000000000 : ℝ) (502108973727/1000000000000 : ℝ) (251054486867/500000000000 : ℝ) (494876441803/1000000000000 : ℝ) (494876441811/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 2 (502108973727/1000000000000 : ℝ) (251054486867/500000000000 : ℝ) (494876441803/1000000000000 : ℝ) (494876441811/1000000000000 : ℝ) (99698541553/200000000000 : ℝ) (498492707773/1000000000000 : ℝ) (49847959067/100000000000 : ℝ) (498479590679/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 3 (99698541553/200000000000 : ℝ) (498492707773/1000000000000 : ℝ) (49847959067/100000000000 : ℝ) (498479590679/1000000000000 : ℝ) (498486149217/1000000000000 : ℝ) (249243074613/500000000000 : ℝ) (249243074587/500000000000 : ℝ) (498486149183/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 4 (498486149217/1000000000000 : ℝ) (249243074613/500000000000 : ℝ) (249243074587/500000000000 : ℝ) (498486149183/1000000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 5 (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 6 (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (63/512 : ℝ))) 7 (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (63/512 : ℝ)) hmem 8 (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (63/512 : ℝ))) hcmem 8 (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (63/512 : ℝ)) (248088434607/250000000000 : ℝ) (992353738431/1000000000000 : ℝ) (99697229839/200000000000 : ℝ) (99697229841/200000000000 : ℝ) (197263380433/250000000000 : ℝ) (789053521751/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0106_exp_lower
  have heNumeric : (513740418057/250000000000 : ℝ)/4 ≤ Real.exp (-5328297314633/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513740418057/250000000000 : ℝ)/4 ≤ Real.exp ((4031/32768 : ℝ)-(789053521751/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4031/32768 : ℝ) (63/512 : ℝ) (789053521751/1000000000000 : ℝ) (513740418057/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0107; no trusted numerical premise.
theorem cover8_leaf0107_exp_radius : (998078763682728083/1000000000000000000 : ℝ) ≤ Real.exp ((-4033/262144 : ℝ)/8) ∧ Real.exp ((-4033/262144 : ℝ)/8) ≤ (249519690920682021/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4033/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0107_exp_lower : (230029181274700109/250000000000000000 : ℝ) ≤ Real.exp ((-666037935037/1000000000000 : ℝ)/8) ∧ Real.exp ((-666037935037/1000000000000 : ℝ)/8) ≤ (920116725098800437/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666037935037/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0107_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027480044227/500000000000 : ℝ) ≤ 4*Real.exp (63/512 : ℝ)*Real.exp (-mu (radius 8 (4033/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027480044227/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4033/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0107_exp_radius
  have hrNumeric : (984733065457/1000000000000 : ℝ) ≤ Real.exp (-4033/262144 : ℝ) ∧ Real.exp (-4033/262144 : ℝ) ≤ (492366532729/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984733065457/1000000000000 : ℝ) ≤ (radius 8 (4033/32768 : ℝ)) ∧ (radius 8 (4033/32768 : ℝ)) ≤ (492366532729/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4033/32768 : ℝ)) (984733065457/1000000000000 : ℝ) (492366532729/500000000000 : ℝ) (174071220463/1000000000000 : ℝ) (17407122047/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4033/32768 : ℝ)) (984733065457/1000000000000 : ℝ) (492366532729/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984733065457/1000000000000 : ℝ) (492366532729/500000000000 : ℝ) (124045816591/125000000000 : ℝ) (992366532729/1000000000000 : ℝ) (992337173271/1000000000000 : ℝ) (992337173273/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 1 (124045816591/125000000000 : ℝ) (992366532729/1000000000000 : ℝ) (992337173271/1000000000000 : ℝ) (992337173273/1000000000000 : ℝ) (992351852999/1000000000000 : ℝ) (992351853001/1000000000000 : ℝ) (99235185289/100000000000 : ℝ) (992351852893/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 2 (992351852999/1000000000000 : ℝ) (992351853001/1000000000000 : ℝ) (99235185289/100000000000 : ℝ) (992351852893/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 3 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 4 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 5 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 6 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4033/32768 : ℝ)) 7 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4033/32768 : ℝ))) (174071220463/1000000000000 : ℝ) (17407122047/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174071220463/1000000000000 : ℝ) (17407122047/100000000000 : ℝ) (587035610231/1000000000000 : ℝ) (117407122047/200000000000 : ℝ) (208609216277/500000000000 : ℝ) (417218432563/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 1 (587035610231/1000000000000 : ℝ) (117407122047/200000000000 : ℝ) (208609216277/500000000000 : ℝ) (417218432563/1000000000000 : ℝ) (31382938837/62500000000 : ℝ) (502127021399/1000000000000 : ℝ) (494896026609/1000000000000 : ℝ) (494896026617/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 2 (31382938837/62500000000 : ℝ) (502127021399/1000000000000 : ℝ) (494896026609/1000000000000 : ℝ) (494896026617/1000000000000 : ℝ) (124627881/250000000 : ℝ) (62313940501/125000000000 : ℝ) (31156150811/62500000000 : ℝ) (62312301623/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 3 (124627881/250000000 : ℝ) (62313940501/125000000000 : ℝ) (31156150811/62500000000 : ℝ) (62312301623/125000000000 : ℝ) (62313121061/125000000000 : ℝ) (31156560531/62500000000 : ℝ) (124626242111/250000000000 : ℝ) (498504968453/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 4 (62313121061/125000000000 : ℝ) (31156560531/62500000000 : ℝ) (124626242111/250000000000 : ℝ) (498504968453/1000000000000 : ℝ) (249252484233/500000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 5 (249252484233/500000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 6 (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4033/32768 : ℝ))) 7 (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4033/32768 : ℝ)) hmem 8 (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4033/32768 : ℝ))) hcmem 8 (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4033/32768 : ℝ)) (62021990809/62500000000 : ℝ) (992351852947/1000000000000 : ℝ) (99700993693/200000000000 : ℝ) (19940198739/40000000000 : ℝ) (394542405009/500000000000 : ℝ) (789084810037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0107_exp_lower
  have heNumeric : (1027480044227/500000000000 : ℝ)/4 ≤ Real.exp (-666037935037/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027480044227/500000000000 : ℝ)/4 ≤ Real.exp ((63/512 : ℝ)-(789084810037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (63/512 : ℝ) (4033/32768 : ℝ) (789084810037/1000000000000 : ℝ) (1027480044227/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0108; no trusted numerical premise.
theorem cover8_leaf0108_exp_radius : (499039143880900107/500000000000000000 : ℝ) ≤ Real.exp ((-2017/131072 : ℝ)/8) ∧ Real.exp ((-2017/131072 : ℝ)/8) ≤ (199615657552360043/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2017/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0108_exp_lower : (920116637063545957/1000000000000000000 : ℝ) ≤ Real.exp ((-5328309603711/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328309603711/8000000000000 : ℝ)/8) ≤ (460058318531772979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328309603711/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0108_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054958515533/1000000000000 : ℝ) ≤ 4*Real.exp (4033/32768 : ℝ)*Real.exp (-mu (radius 8 (2017/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054958515533/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2017/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0108_exp_radius
  have hrNumeric : (492364654503/500000000000 : ℝ) ≤ Real.exp (-2017/131072 : ℝ) ∧ Real.exp (-2017/131072 : ℝ) ≤ (984729309007/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492364654503/500000000000 : ℝ) ≤ (radius 8 (2017/16384 : ℝ)) ∧ (radius 8 (2017/16384 : ℝ)) ≤ (984729309007/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2017/16384 : ℝ)) (492364654503/500000000000 : ℝ) (984729309007/1000000000000 : ℝ) (1360097419/7812500000 : ℝ) (87046234819/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2017/16384 : ℝ)) (492364654503/500000000000 : ℝ) (984729309007/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492364654503/500000000000 : ℝ) (984729309007/1000000000000 : ℝ) (992364654503/1000000000000 : ℝ) (124045581813/125000000000 : ℝ) (49616764027/50000000000 : ℝ) (496167640271/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 1 (992364654503/1000000000000 : ℝ) (124045581813/125000000000 : ℝ) (49616764027/50000000000 : ℝ) (496167640271/500000000000 : ℝ) (992349967521/1000000000000 : ℝ) (992349967523/1000000000000 : ℝ) (248087491853/250000000000 : ℝ) (198469993483/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 2 (992349967521/1000000000000 : ℝ) (992349967523/1000000000000 : ℝ) (248087491853/250000000000 : ℝ) (198469993483/200000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 3 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 4 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 5 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 6 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2017/16384 : ℝ)) 7 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2017/16384 : ℝ))) (1360097419/7812500000 : ℝ) (87046234819/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1360097419/7812500000 : ℝ) (87046234819/500000000000 : ℝ) (9172597419/15625000000 : ℝ) (587046234819/1000000000000 : ℝ) (417243897057/1000000000000 : ℝ) (208621948533/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 1 (9172597419/15625000000 : ℝ) (587046234819/1000000000000 : ℝ) (417243897057/1000000000000 : ℝ) (208621948533/500000000000 : ℝ) (31384066621/62500000000 : ℝ) (502145065943/1000000000000 : ℝ) (247457803861/500000000000 : ℝ) (49491560773/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 2 (31384066621/62500000000 : ℝ) (502145065943/1000000000000 : ℝ) (247457803861/500000000000 : ℝ) (49491560773/100000000000 : ℝ) (498530336829/1000000000000 : ℝ) (498530336837/1000000000000 : ℝ) (49851723187/100000000000 : ℝ) (498517231879/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 3 (498530336829/1000000000000 : ℝ) (498530336837/1000000000000 : ℝ) (49851723187/100000000000 : ℝ) (498517231879/1000000000000 : ℝ) (498523784349/1000000000000 : ℝ) (249261892179/500000000000 : ℝ) (249261892153/500000000000 : ℝ) (99704756863/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 4 (498523784349/1000000000000 : ℝ) (249261892179/500000000000 : ℝ) (249261892153/500000000000 : ℝ) (99704756863/200000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 5 (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 6 (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2017/16384 : ℝ))) 7 (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2017/16384 : ℝ)) hmem 8 (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2017/16384 : ℝ))) hcmem 8 (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2017/16384 : ℝ)) (496174983733/500000000000 : ℝ) (992349967469/1000000000000 : ℝ) (498523784327/1000000000000 : ℝ) (498523784337/1000000000000 : ℝ) (789116093023/1000000000000 : ℝ) (394558046521/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0108_exp_lower
  have heNumeric : (2054958515533/1000000000000 : ℝ)/4 ≤ Real.exp (-5328309603711/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054958515533/1000000000000 : ℝ)/4 ≤ Real.exp ((4033/32768 : ℝ)-(394558046521/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4033/32768 : ℝ) (2017/16384 : ℝ) (394558046521/500000000000 : ℝ) (2054958515533/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0109; no trusted numerical premise.
theorem cover8_leaf0109_exp_radius : (499038905920549641/500000000000000000 : ℝ) ≤ Real.exp ((-4035/262144 : ℝ)/8) ∧ Real.exp ((-4035/262144 : ℝ)/8) ≤ (998077811841099283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4035/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0109_exp_lower : (57507284352180421/62500000000000000 : ℝ) ≤ Real.exp ((-2664157842467/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664157842467/4000000000000 : ℝ)/8) ≤ (920116549634886737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664157842467/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0109_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054956953451/1000000000000 : ℝ) ≤ 4*Real.exp (2017/16384 : ℝ)*Real.exp (-mu (radius 8 (4035/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054956953451/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4035/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0109_exp_radius
  have hrNumeric : (984725552569/1000000000000 : ℝ) ≤ Real.exp (-4035/262144 : ℝ) ∧ Real.exp (-4035/262144 : ℝ) ≤ (98472555257/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984725552569/1000000000000 : ℝ) ≤ (radius 8 (4035/32768 : ℝ)) ∧ (radius 8 (4035/32768 : ℝ)) ≤ (98472555257/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4035/32768 : ℝ)) (984725552569/1000000000000 : ℝ) (98472555257/100000000000 : ℝ) (174113716047/1000000000000 : ℝ) (174113716053/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4035/32768 : ℝ)) (984725552569/1000000000000 : ℝ) (98472555257/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984725552569/1000000000000 : ℝ) (98472555257/100000000000 : ℝ) (248090694071/250000000000 : ℝ) (198472555257/200000000000 : ℝ) (992333387813/1000000000000 : ℝ) (496166693907/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 1 (248090694071/250000000000 : ℝ) (198472555257/200000000000 : ℝ) (992333387813/1000000000000 : ℝ) (496166693907/500000000000 : ℝ) (7752719391/7812500000 : ℝ) (19846961641/20000000000 : ℝ) (992348081939/1000000000000 : ℝ) (992348081941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 2 (7752719391/7812500000 : ℝ) (19846961641/20000000000 : ℝ) (992348081939/1000000000000 : ℝ) (992348081941/1000000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 3 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 4 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 5 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 6 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4035/32768 : ℝ)) 7 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4035/32768 : ℝ))) (174113716047/1000000000000 : ℝ) (174113716053/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174113716047/1000000000000 : ℝ) (174113716053/1000000000000 : ℝ) (587056858023/1000000000000 : ℝ) (587056858027/1000000000000 : ℝ) (417269356707/1000000000000 : ℝ) (83453871343/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 1 (587056858023/1000000000000 : ℝ) (587056858027/1000000000000 : ℝ) (417269356707/1000000000000 : ℝ) (83453871343/200000000000 : ℝ) (100432621473/200000000000 : ℝ) (502163107371/1000000000000 : ℝ) (123733796287/250000000000 : ℝ) (98987037031/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 2 (100432621473/200000000000 : ℝ) (502163107371/1000000000000 : ℝ) (123733796287/250000000000 : ℝ) (98987037031/200000000000 : ℝ) (31159321641/62500000000 : ℝ) (498549146263/1000000000000 : ℝ) (389481287/781250000 : ℝ) (62317005921/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 3 (31159321641/62500000000 : ℝ) (498549146263/1000000000000 : ℝ) (389481287/781250000 : ℝ) (62317005921/125000000000 : ℝ) (62317824601/125000000000 : ℝ) (31158912301/62500000000 : ℝ) (124635649191/250000000000 : ℝ) (498542596773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 4 (62317824601/125000000000 : ℝ) (31158912301/62500000000 : ℝ) (124635649191/250000000000 : ℝ) (498542596773/1000000000000 : ℝ) (249271298393/500000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 5 (249271298393/500000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 6 (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4035/32768 : ℝ))) 7 (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4035/32768 : ℝ)) hmem 8 (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4035/32768 : ℝ))) hcmem 8 (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4035/32768 : ℝ)) (992348081993/1000000000000 : ℝ) (248087020499/250000000000 : ℝ) (99708519357/200000000000 : ℝ) (99708519359/200000000000 : ℝ) (394573685377/500000000000 : ℝ) (789147370773/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0109_exp_lower
  have heNumeric : (2054956953451/1000000000000 : ℝ)/4 ≤ Real.exp (-2664157842467/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054956953451/1000000000000 : ℝ)/4 ≤ Real.exp ((2017/16384 : ℝ)-(789147370773/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2017/16384 : ℝ) (4035/32768 : ℝ) (789147370773/1000000000000 : ℝ) (2054956953451/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0110; no trusted numerical premise.
theorem cover8_leaf0110_exp_radius : (499038667960312643/500000000000000000 : ℝ) ≤ Real.exp ((-1009/65536 : ℝ)/8) ∧ Real.exp ((-1009/65536 : ℝ)/8) ≤ (998077335920625287/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1009/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0110_exp_lower : (28753639462879141/31250000000000000 : ℝ) ≤ Real.exp ((-5328321724013/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328321724013/8000000000000 : ℝ)/8) ≤ (920116462812132513/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328321724013/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0110_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410991080439/200000000000 : ℝ) ≤ 4*Real.exp (4035/32768 : ℝ)*Real.exp (-mu (radius 8 (1009/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410991080439/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1009/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0110_exp_radius
  have hrNumeric : (492360898073/500000000000 : ℝ) ≤ Real.exp (-1009/65536 : ℝ) ∧ Real.exp (-1009/65536 : ℝ) ≤ (984721796147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492360898073/500000000000 : ℝ) ≤ (radius 8 (1009/8192 : ℝ)) ∧ (radius 8 (1009/8192 : ℝ)) ≤ (984721796147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1009/8192 : ℝ)) (492360898073/500000000000 : ℝ) (984721796147/1000000000000 : ℝ) (174134959709/1000000000000 : ℝ) (43533739929/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1009/8192 : ℝ)) (492360898073/500000000000 : ℝ) (984721796147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492360898073/500000000000 : ℝ) (984721796147/1000000000000 : ℝ) (992360898073/1000000000000 : ℝ) (496180449037/500000000000 : ℝ) (992331495089/1000000000000 : ℝ) (99233149509/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 1 (992360898073/1000000000000 : ℝ) (496180449037/500000000000 : ℝ) (992331495089/1000000000000 : ℝ) (99233149509/100000000000 : ℝ) (992346196581/1000000000000 : ℝ) (496173098291/500000000000 : ℝ) (124043274559/125000000000 : ℝ) (496173098237/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 2 (992346196581/1000000000000 : ℝ) (496173098291/500000000000 : ℝ) (124043274559/125000000000 : ℝ) (496173098237/500000000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 3 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 4 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 5 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 6 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1009/8192 : ℝ)) 7 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1009/8192 : ℝ))) (174134959709/1000000000000 : ℝ) (43533739929/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174134959709/1000000000000 : ℝ) (43533739929/250000000000 : ℝ) (293533739927/500000000000 : ℝ) (293533739929/500000000000 : ℝ) (83458962301/200000000000 : ℝ) (208647405757/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 1 (293533739927/500000000000 : ℝ) (293533739929/500000000000 : ℝ) (83458962301/200000000000 : ℝ) (208647405757/500000000000 : ℝ) (502181145679/1000000000000 : ℝ) (251090572843/500000000000 : ℝ) (61869344861/125000000000 : ℝ) (30934672431/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 2 (502181145679/1000000000000 : ℝ) (251090572843/500000000000 : ℝ) (61869344861/125000000000 : ℝ) (30934672431/62500000000 : ℝ) (498567952283/1000000000000 : ℝ) (498567952291/1000000000000 : ℝ) (249277429723/500000000000 : ℝ) (249277429727/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 3 (498567952283/1000000000000 : ℝ) (498567952291/1000000000000 : ℝ) (249277429723/500000000000 : ℝ) (249277429727/500000000000 : ℝ) (62320175733/125000000000 : ℝ) (498561405873/1000000000000 : ℝ) (498561405821/1000000000000 : ℝ) (49856140583/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 4 (62320175733/125000000000 : ℝ) (498561405873/1000000000000 : ℝ) (498561405821/1000000000000 : ℝ) (49856140583/100000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 5 (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 6 (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1009/8192 : ℝ))) 7 (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1009/8192 : ℝ)) hmem 8 (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1009/8192 : ℝ))) hcmem 8 (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1009/8192 : ℝ)) (496173098263/500000000000 : ℝ) (62021637283/62500000000 : ℝ) (249280702921/500000000000 : ℝ) (124640351463/250000000000 : ℝ) (789178643217/1000000000000 : ℝ) (197294660809/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0110_exp_lower
  have heNumeric : (410991080439/200000000000 : ℝ)/4 ≤ Real.exp (-5328321724013/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410991080439/200000000000 : ℝ)/4 ≤ Real.exp ((4035/32768 : ℝ)-(197294660809/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4035/32768 : ℝ) (1009/8192 : ℝ) (197294660809/250000000000 : ℝ) (410991080439/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0111; no trusted numerical premise.
theorem cover8_leaf0111_exp_radius : (998076860000378227/1000000000000000000 : ℝ) ≤ Real.exp ((-4037/262144 : ℝ)/8) ∧ Real.exp ((-4037/262144 : ℝ)/8) ≤ (249519215000094557/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4037/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0111_exp_lower : (920116376596088217/1000000000000000000 : ℝ) ≤ Real.exp ((-1332081930223/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332081930223/2000000000000 : ℝ)/8) ≤ (460058188298044109/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332081930223/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0111_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054953861781/1000000000000 : ℝ) ≤ 4*Real.exp (1009/8192 : ℝ)*Real.exp (-mu (radius 8 (4037/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054953861781/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4037/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0111_exp_radius
  have hrNumeric : (492359019869/500000000000 : ℝ) ≤ Real.exp (-4037/262144 : ℝ) ∧ Real.exp (-4037/262144 : ℝ) ≤ (984718039739/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492359019869/500000000000 : ℝ) ≤ (radius 8 (4037/32768 : ℝ)) ∧ (radius 8 (4037/32768 : ℝ)) ≤ (984718039739/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4037/32768 : ℝ)) (492359019869/500000000000 : ℝ) (984718039739/1000000000000 : ℝ) (87078100307/500000000000 : ℝ) (174156200621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4037/32768 : ℝ)) (492359019869/500000000000 : ℝ) (984718039739/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492359019869/500000000000 : ℝ) (984718039739/1000000000000 : ℝ) (992359019869/1000000000000 : ℝ) (99235901987/100000000000 : ℝ) (992329602369/1000000000000 : ℝ) (99232960237/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 1 (992359019869/1000000000000 : ℝ) (99235901987/100000000000 : ℝ) (992329602369/1000000000000 : ℝ) (99232960237/100000000000 : ℝ) (992344311119/1000000000000 : ℝ) (12404303889/12500000000 : ℝ) (992344311009/1000000000000 : ℝ) (992344311011/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 2 (992344311119/1000000000000 : ℝ) (12404303889/12500000000 : ℝ) (992344311009/1000000000000 : ℝ) (992344311011/1000000000000 : ℝ) (124043038883/125000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 3 (124043038883/125000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 4 (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 5 (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 6 (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4037/32768 : ℝ)) 7 (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4037/32768 : ℝ))) (87078100307/500000000000 : ℝ) (174156200621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87078100307/500000000000 : ℝ) (174156200621/1000000000000 : ℝ) (587078100307/1000000000000 : ℝ) (587078100311/1000000000000 : ℝ) (208660130723/500000000000 : ℝ) (26082516341/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 1 (587078100307/1000000000000 : ℝ) (587078100311/1000000000000 : ℝ) (208660130723/500000000000 : ℝ) (26082516341/62500000000 : ℝ) (125549795219/250000000000 : ℝ) (125549795221/250000000000 : ℝ) (494974328939/1000000000000 : ℝ) (123743582237/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 2 (125549795219/250000000000 : ℝ) (125549795221/250000000000 : ℝ) (494974328939/1000000000000 : ℝ) (123743582237/250000000000 : ℝ) (498586754907/1000000000000 : ℝ) (124646688729/250000000000 : ℝ) (797717869/1600000000 : ℝ) (249286834067/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 3 (498586754907/1000000000000 : ℝ) (124646688729/250000000000 : ℝ) (797717869/1600000000 : ℝ) (249286834067/500000000000 : ℝ) (124645052879/250000000000 : ℝ) (19943208461/40000000000 : ℝ) (498580211473/1000000000000 : ℝ) (498580211483/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 4 (124645052879/250000000000 : ℝ) (19943208461/40000000000 : ℝ) (498580211473/1000000000000 : ℝ) (498580211483/1000000000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 5 (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 6 (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4037/32768 : ℝ))) 7 (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4037/32768 : ℝ)) hmem 8 (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4037/32768 : ℝ))) hcmem 8 (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4037/32768 : ℝ)) (992344311063/1000000000000 : ℝ) (496172155533/500000000000 : ℝ) (249290105747/500000000000 : ℝ) (31161263219/62500000000 : ℝ) (157841982081/200000000000 : ℝ) (98651238803/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0111_exp_lower
  have heNumeric : (2054953861781/1000000000000 : ℝ)/4 ≤ Real.exp (-1332081930223/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054953861781/1000000000000 : ℝ)/4 ≤ Real.exp ((1009/8192 : ℝ)-(98651238803/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1009/8192 : ℝ) (4037/32768 : ℝ) (98651238803/125000000000 : ℝ) (2054953861781/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0112; no trusted numerical premise.
theorem cover8_leaf0112_exp_radius : (124759548010044763/125000000000000000 : ℝ) ≤ Real.exp ((-2019/131072 : ℝ)/8) ∧ Real.exp ((-2019/131072 : ℝ)/8) ≤ (199615276816071621/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2019/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0112_exp_lower : (184023258197120707/200000000000000000 : ℝ) ≤ Real.exp ((-5328333675651/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328333675651/8000000000000 : ℝ)/8) ≤ (57507268186600221/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328333675651/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0112_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054952332187/1000000000000 : ℝ) ≤ 4*Real.exp (4037/32768 : ℝ)*Real.exp (-mu (radius 8 (2019/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054952332187/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2019/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0112_exp_radius
  have hrNumeric : (61544642709/62500000000 : ℝ) ≤ Real.exp (-2019/131072 : ℝ) ∧ Real.exp (-2019/131072 : ℝ) ≤ (196942856669/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61544642709/62500000000 : ℝ) ≤ (radius 8 (2019/16384 : ℝ)) ∧ (radius 8 (2019/16384 : ℝ)) ≤ (196942856669/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2019/16384 : ℝ)) (61544642709/62500000000 : ℝ) (196942856669/200000000000 : ℝ) (174177438769/1000000000000 : ℝ) (21772179847/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2019/16384 : ℝ)) (61544642709/62500000000 : ℝ) (196942856669/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61544642709/62500000000 : ℝ) (196942856669/200000000000 : ℝ) (124044642709/125000000000 : ℝ) (992357141673/1000000000000 : ℝ) (248081927413/250000000000 : ℝ) (992327709653/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 1 (124044642709/125000000000 : ℝ) (992357141673/1000000000000 : ℝ) (248081927413/250000000000 : ℝ) (992327709653/1000000000000 : ℝ) (496171212831/500000000000 : ℝ) (992342425663/1000000000000 : ℝ) (62021401597/62500000000 : ℝ) (496171212777/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 2 (496171212831/500000000000 : ℝ) (992342425663/1000000000000 : ℝ) (62021401597/62500000000 : ℝ) (496171212777/500000000000 : ℝ) (992342425607/1000000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 3 (992342425607/1000000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 4 (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 5 (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 6 (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2019/16384 : ℝ)) 7 (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2019/16384 : ℝ))) (174177438769/1000000000000 : ℝ) (21772179847/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174177438769/1000000000000 : ℝ) (21772179847/125000000000 : ℝ) (73386089923/125000000000 : ℝ) (146772179847/250000000000 : ℝ) (417345706541/1000000000000 : ℝ) (417345706551/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 1 (73386089923/125000000000 : ℝ) (146772179847/250000000000 : ℝ) (417345706541/1000000000000 : ℝ) (417345706551/1000000000000 : ℝ) (251108606481/500000000000 : ℝ) (50221721297/100000000000 : ℝ) (494993895309/1000000000000 : ℝ) (247496947659/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 2 (251108606481/500000000000 : ℝ) (50221721297/100000000000 : ℝ) (494993895309/1000000000000 : ℝ) (247496947659/500000000000 : ℝ) (99721110827/200000000000 : ℝ) (15581423567/31250000000 : ℝ) (124648118351/250000000000 : ℝ) (498592473413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 3 (99721110827/200000000000 : ℝ) (15581423567/31250000000 : ℝ) (124648118351/250000000000 : ℝ) (498592473413/1000000000000 : ℝ) (498599013769/1000000000000 : ℝ) (498599013779/1000000000000 : ℝ) (249299506863/500000000000 : ℝ) (62324876717/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 4 (498599013769/1000000000000 : ℝ) (498599013779/1000000000000 : ℝ) (249299506863/500000000000 : ℝ) (62324876717/125000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 5 (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 6 (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2019/16384 : ℝ))) 7 (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2019/16384 : ℝ)) hmem 8 (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2019/16384 : ℝ))) hcmem 8 (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2019/16384 : ℝ)) (496171212803/500000000000 : ℝ) (992342425609/1000000000000 : ℝ) (498599013747/1000000000000 : ℝ) (249299506879/500000000000 : ℝ) (394620586163/500000000000 : ℝ) (789241172347/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0112_exp_lower
  have heNumeric : (2054952332187/1000000000000 : ℝ)/4 ≤ Real.exp (-5328333675651/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054952332187/1000000000000 : ℝ)/4 ≤ Real.exp ((4037/32768 : ℝ)-(789241172347/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4037/32768 : ℝ) (2019/16384 : ℝ) (789241172347/1000000000000 : ℝ) (2054952332187/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0113; no trusted numerical premise.
theorem cover8_leaf0113_exp_radius : (499037954080282459/500000000000000000 : ℝ) ≤ Real.exp ((-4039/262144 : ℝ)/8) ∧ Real.exp ((-4039/262144 : ℝ)/8) ≤ (998075908160564919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4039/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0113_exp_lower : (920116205980563281/1000000000000000000 : ℝ) ≤ Real.exp ((-2664169794149/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664169794149/4000000000000 : ℝ)/8) ≤ (460058102990281641/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664169794149/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0113_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513737703353/250000000000 : ℝ) ≤ 4*Real.exp (2019/16384 : ℝ)*Real.exp (-mu (radius 8 (4039/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513737703353/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4039/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0113_exp_radius
  have hrNumeric : (246177631741/250000000000 : ℝ) ≤ Real.exp (-4039/262144 : ℝ) ∧ Real.exp (-4039/262144 : ℝ) ≤ (196942105393/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246177631741/250000000000 : ℝ) ≤ (radius 8 (4039/32768 : ℝ)) ∧ (radius 8 (4039/32768 : ℝ)) ≤ (196942105393/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4039/32768 : ℝ)) (246177631741/250000000000 : ℝ) (196942105393/200000000000 : ℝ) (87099337087/500000000000 : ℝ) (174198674181/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4039/32768 : ℝ)) (246177631741/250000000000 : ℝ) (196942105393/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246177631741/250000000000 : ℝ) (196942105393/200000000000 : ℝ) (496177631741/500000000000 : ℝ) (992355263483/1000000000000 : ℝ) (992325816939/1000000000000 : ℝ) (49616290847/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 1 (496177631741/500000000000 : ℝ) (992355263483/1000000000000 : ℝ) (992325816939/1000000000000 : ℝ) (49616290847/50000000000 : ℝ) (99234054021/100000000000 : ℝ) (248085135053/250000000000 : ℝ) (992340540101/1000000000000 : ℝ) (992340540103/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 2 (99234054021/100000000000 : ℝ) (248085135053/250000000000 : ℝ) (992340540101/1000000000000 : ℝ) (992340540103/1000000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 3 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 4 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 5 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 6 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4039/32768 : ℝ)) 7 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4039/32768 : ℝ))) (87099337087/500000000000 : ℝ) (174198674181/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87099337087/500000000000 : ℝ) (174198674181/1000000000000 : ℝ) (587099337087/1000000000000 : ℝ) (587099337091/1000000000000 : ℝ) (417371146791/1000000000000 : ℝ) (1043427867/2500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 1 (587099337087/1000000000000 : ℝ) (587099337091/1000000000000 : ℝ) (417371146791/1000000000000 : ℝ) (1043427867/2500000000 : ℝ) (502235241939/1000000000000 : ℝ) (251117620973/500000000000 : ℝ) (495013457999/1000000000000 : ℝ) (495013458007/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 2 (502235241939/1000000000000 : ℝ) (251117620973/500000000000 : ℝ) (495013457999/1000000000000 : ℝ) (495013458007/1000000000000 : ℝ) (498624349969/1000000000000 : ℝ) (498624349977/1000000000000 : ℝ) (124652818821/250000000000 : ℝ) (498611275293/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 3 (498624349969/1000000000000 : ℝ) (498624349977/1000000000000 : ℝ) (124652818821/250000000000 : ℝ) (498611275293/1000000000000 : ℝ) (249308906313/500000000000 : ℝ) (99723562527/200000000000 : ℝ) (498617812583/1000000000000 : ℝ) (498617812593/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 4 (249308906313/500000000000 : ℝ) (99723562527/200000000000 : ℝ) (498617812583/1000000000000 : ℝ) (498617812593/1000000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 5 (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 6 (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4039/32768 : ℝ))) 7 (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4039/32768 : ℝ)) hmem 8 (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4039/32768 : ℝ))) hcmem 8 (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4039/32768 : ℝ)) (198468108031/200000000000 : ℝ) (496170270079/500000000000 : ℝ) (124654453151/250000000000 : ℝ) (249308906307/500000000000 : ℝ) (789272428987/1000000000000 : ℝ) (394636214503/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0113_exp_lower
  have heNumeric : (513737703353/250000000000 : ℝ)/4 ≤ Real.exp (-2664169794149/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513737703353/250000000000 : ℝ)/4 ≤ Real.exp ((2019/16384 : ℝ)-(394636214503/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2019/16384 : ℝ) (4039/32768 : ℝ) (394636214503/500000000000 : ℝ) (513737703353/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0114; no trusted numerical premise.
theorem cover8_leaf0114_exp_radius : (249518858060249667/250000000000000000 : ℝ) ≤ Real.exp ((-505/32768 : ℝ)/8) ∧ Real.exp ((-505/32768 : ℝ)/8) ≤ (998075432240998669/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-505/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0114_exp_lower : (460058060790713673/500000000000000000 : ℝ) ≤ Real.exp ((-5328345458801/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328345458801/8000000000000 : ℝ)/8) ≤ (920116121581427347/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328345458801/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0114_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054949305463/1000000000000 : ℝ) ≤ 4*Real.exp (4039/32768 : ℝ)*Real.exp (-mu (radius 8 (505/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054949305463/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (505/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0114_exp_radius
  have hrNumeric : (984706770599/1000000000000 : ℝ) ≤ Real.exp (-505/32768 : ℝ) ∧ Real.exp (-505/32768 : ℝ) ≤ (4923533853/5000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984706770599/1000000000000 : ℝ) ≤ (radius 8 (505/4096 : ℝ)) ∧ (radius 8 (505/4096 : ℝ)) ≤ (4923533853/5000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (505/4096 : ℝ)) (984706770599/1000000000000 : ℝ) (4923533853/5000000000 : ℝ) (87109953413/500000000000 : ℝ) (10888744177/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (505/4096 : ℝ)) (984706770599/1000000000000 : ℝ) (4923533853/5000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (505/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984706770599/1000000000000 : ℝ) (4923533853/5000000000 : ℝ) (992353385299/1000000000000 : ℝ) (9923533853/10000000000 : ℝ) (992323924229/1000000000000 : ℝ) (992323924231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (505/4096 : ℝ)) 1 (992353385299/1000000000000 : ℝ) (9923533853/10000000000 : ℝ) (992323924229/1000000000000 : ℝ) (992323924231/1000000000000 : ℝ) (248084663691/250000000000 : ℝ) (496169327383/500000000000 : ℝ) (496169327327/500000000000 : ℝ) (992338654657/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (505/4096 : ℝ)) 2 (248084663691/250000000000 : ℝ) (496169327383/500000000000 : ℝ) (496169327327/500000000000 : ℝ) (992338654657/1000000000000 : ℝ) (992338654709/1000000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (505/4096 : ℝ)) 3 (992338654709/1000000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (505/4096 : ℝ)) 4 (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (505/4096 : ℝ)) 5 (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (505/4096 : ℝ)) 6 (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (505/4096 : ℝ)) 7 (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (505/4096 : ℝ))) (87109953413/500000000000 : ℝ) (10888744177/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87109953413/500000000000 : ℝ) (10888744177/62500000000 : ℝ) (587109953413/1000000000000 : ℝ) (73388744177/125000000000 : ℝ) (26087286387/62500000000 : ℝ) (2086982911/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 1 (587109953413/1000000000000 : ℝ) (73388744177/125000000000 : ℝ) (26087286387/62500000000 : ℝ) (2086982911/5000000000 : ℝ) (251126633901/500000000000 : ℝ) (15695414619/31250000000 : ℝ) (99006603401/200000000000 : ℝ) (123758254253/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 2 (251126633901/500000000000 : ℝ) (15695414619/31250000000 : ℝ) (99006603401/200000000000 : ℝ) (123758254253/250000000000 : ℝ) (498643142403/1000000000000 : ℝ) (49864314241/100000000000 : ℝ) (249315036881/500000000000 : ℝ) (49863007377/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 3 (498643142403/1000000000000 : ℝ) (49864314241/100000000000 : ℝ) (249315036881/500000000000 : ℝ) (49863007377/100000000000 : ℝ) (249318304041/500000000000 : ℝ) (49863660809/100000000000 : ℝ) (498636608039/1000000000000 : ℝ) (31164788003/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 4 (249318304041/500000000000 : ℝ) (49863660809/100000000000 : ℝ) (498636608039/1000000000000 : ℝ) (31164788003/62500000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 5 (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 6 (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (505/4096 : ℝ))) 7 (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (505/4096 : ℝ)) hmem 8 (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (505/4096 : ℝ))) hcmem 8 (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (505/4096 : ℝ)) (248084663677/250000000000 : ℝ) (124042331839/125000000000 : ℝ) (24931830403/50000000000 : ℝ) (498636608069/1000000000000 : ℝ) (394651840189/500000000000 : ℝ) (789303680397/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0114_exp_lower
  have heNumeric : (2054949305463/1000000000000 : ℝ)/4 ≤ Real.exp (-5328345458801/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054949305463/1000000000000 : ℝ)/4 ≤ Real.exp ((4039/32768 : ℝ)-(789303680397/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4039/32768 : ℝ) (505/4096 : ℝ) (789303680397/1000000000000 : ℝ) (2054949305463/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0115; no trusted numerical premise.
theorem cover8_leaf0115_exp_radius : (998074956321659353/1000000000000000000 : ℝ) ≤ Real.exp ((-4041/262144 : ℝ)/8) ∧ Real.exp ((-4041/262144 : ℝ)/8) ≤ (499037478160829677/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4041/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0115_exp_lower : (230029009446732601/250000000000000000 : ℝ) ≤ Real.exp ((-333021955453/500000000000 : ℝ)/8) ∧ Real.exp ((-333021955453/500000000000 : ℝ)/8) ≤ (184023207557386081/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333021955453/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0115_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027473904159/500000000000 : ℝ) ≤ 4*Real.exp (505/4096 : ℝ)*Real.exp (-mu (radius 8 (4041/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027473904159/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4041/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0115_exp_radius
  have hrNumeric : (123087876781/125000000000 : ℝ) ≤ Real.exp (-4041/262144 : ℝ) ∧ Real.exp (-4041/262144 : ℝ) ≤ (984703014249/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123087876781/125000000000 : ℝ) ≤ (radius 8 (4041/32768 : ℝ)) ∧ (radius 8 (4041/32768 : ℝ)) ≤ (984703014249/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4041/32768 : ℝ)) (123087876781/125000000000 : ℝ) (984703014249/1000000000000 : ℝ) (174241136729/1000000000000 : ℝ) (5445035523/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4041/32768 : ℝ)) (123087876781/125000000000 : ℝ) (984703014249/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123087876781/125000000000 : ℝ) (984703014249/1000000000000 : ℝ) (248087876781/250000000000 : ℝ) (7938812057/8000000000 : ℝ) (248080507881/250000000000 : ℝ) (39692881261/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 1 (248087876781/250000000000 : ℝ) (7938812057/8000000000 : ℝ) (248080507881/250000000000 : ℝ) (39692881261/40000000000 : ℝ) (248084192331/250000000000 : ℝ) (39693470773/40000000000 : ℝ) (496168384607/500000000000 : ℝ) (15505262019/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 2 (248084192331/250000000000 : ℝ) (39693470773/40000000000 : ℝ) (496168384607/500000000000 : ℝ) (15505262019/15625000000 : ℝ) (992336769269/1000000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 3 (992336769269/1000000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 4 (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 5 (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 6 (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4041/32768 : ℝ)) 7 (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4041/32768 : ℝ))) (174241136729/1000000000000 : ℝ) (5445035523/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174241136729/1000000000000 : ℝ) (5445035523/31250000000 : ℝ) (146780142091/250000000000 : ℝ) (36695035523/62500000000 : ℝ) (1669688051/4000000000 : ℝ) (10435550319/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 1 (146780142091/250000000000 : ℝ) (36695035523/62500000000 : ℝ) (1669688051/4000000000 : ℝ) (10435550319/25000000000 : ℝ) (502271290557/1000000000000 : ℝ) (125567822641/250000000000 : ℝ) (123763143083/250000000000 : ℝ) (495052572341/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 2 (502271290557/1000000000000 : ℝ) (125567822641/250000000000 : ℝ) (123763143083/250000000000 : ℝ) (495052572341/1000000000000 : ℝ) (124665482861/250000000000 : ℝ) (498661931453/1000000000000 : ℝ) (498648868843/1000000000000 : ℝ) (124662217213/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 3 (124665482861/250000000000 : ℝ) (498661931453/1000000000000 : ℝ) (498648868843/1000000000000 : ℝ) (124662217213/250000000000 : ℝ) (498655400143/1000000000000 : ℝ) (498655400153/1000000000000 : ℝ) (4986554001/10000000000 : ℝ) (49865540011/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 4 (498655400143/1000000000000 : ℝ) (498655400153/1000000000000 : ℝ) (4986554001/10000000000 : ℝ) (49865540011/100000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 5 (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 6 (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4041/32768 : ℝ))) 7 (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4041/32768 : ℝ)) hmem 8 (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4041/32768 : ℝ))) hcmem 8 (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4041/32768 : ℝ)) (248084192317/250000000000 : ℝ) (992336769271/1000000000000 : ℝ) (498655400121/1000000000000 : ℝ) (124663850033/250000000000 : ℝ) (78933492651/100000000000 : ℝ) (789334926531/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0115_exp_lower
  have heNumeric : (1027473904159/500000000000 : ℝ)/4 ≤ Real.exp (-333021955453/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027473904159/500000000000 : ℝ)/4 ≤ Real.exp ((505/4096 : ℝ)-(789334926531/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (505/4096 : ℝ) (4041/32768 : ℝ) (789334926531/1000000000000 : ℝ) (1027473904159/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0116; no trusted numerical premise.
theorem cover8_leaf0116_exp_radius : (39922979216101879/40000000000000000 : ℝ) ≤ Real.exp ((-2021/131072 : ℝ)/8) ∧ Real.exp ((-2021/131072 : ℝ)/8) ≤ (31189827512579593/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2021/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0116_exp_lower : (36804638183878291/40000000000000000 : ℝ) ≤ Real.exp ((-5328357073647/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328357073647/8000000000000 : ℝ)/8) ≤ (230028988649239319/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328357073647/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0116_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82197852879/40000000000 : ℝ) ≤ 4*Real.exp (4041/32768 : ℝ)*Real.exp (-mu (radius 8 (2021/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (82197852879/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2021/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0116_exp_radius
  have hrNumeric : (984699257911/1000000000000 : ℝ) ≤ Real.exp (-2021/131072 : ℝ) ∧ Real.exp (-2021/131072 : ℝ) ≤ (123087407239/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984699257911/1000000000000 : ℝ) ≤ (radius 8 (2021/16384 : ℝ)) ∧ (radius 8 (2021/16384 : ℝ)) ≤ (123087407239/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2021/16384 : ℝ)) (984699257911/1000000000000 : ℝ) (123087407239/125000000000 : ℝ) (174262363887/1000000000000 : ℝ) (174262363893/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2021/16384 : ℝ)) (984699257911/1000000000000 : ℝ) (123087407239/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984699257911/1000000000000 : ℝ) (123087407239/125000000000 : ℝ) (198469925791/200000000000 : ℝ) (248087407239/250000000000 : ℝ) (992320138821/1000000000000 : ℝ) (992320138823/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 1 (198469925791/200000000000 : ℝ) (248087407239/250000000000 : ℝ) (992320138821/1000000000000 : ℝ) (992320138823/1000000000000 : ℝ) (62020930243/62500000000 : ℝ) (99233488389/100000000000 : ℝ) (496167441889/500000000000 : ℝ) (49616744189/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 2 (62020930243/62500000000 : ℝ) (99233488389/100000000000 : ℝ) (496167441889/500000000000 : ℝ) (49616744189/50000000000 : ℝ) (992334883833/1000000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 3 (992334883833/1000000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 4 (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 5 (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 6 (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2021/16384 : ℝ)) 7 (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2021/16384 : ℝ))) (174262363887/1000000000000 : ℝ) (174262363893/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174262363887/1000000000000 : ℝ) (174262363893/1000000000000 : ℝ) (587131181943/1000000000000 : ℝ) (587131181947/1000000000000 : ℝ) (52180929809/125000000000 : ℝ) (5218092981/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 1 (587131181943/1000000000000 : ℝ) (587131181947/1000000000000 : ℝ) (52180929809/125000000000 : ℝ) (5218092981/12500000000 : ℝ) (502289310207/1000000000000 : ℝ) (251144655107/500000000000 : ℝ) (495072123987/1000000000000 : ℝ) (247536061997/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 2 (502289310207/1000000000000 : ℝ) (251144655107/500000000000 : ℝ) (495072123987/1000000000000 : ℝ) (247536061997/500000000000 : ℝ) (498680717097/1000000000000 : ℝ) (31167544819/62500000000 : ℝ) (498667660531/1000000000000 : ℝ) (498667660539/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 3 (498680717097/1000000000000 : ℝ) (31167544819/62500000000 : ℝ) (498667660531/1000000000000 : ℝ) (498667660539/1000000000000 : ℝ) (249337094407/500000000000 : ℝ) (249337094411/500000000000 : ℝ) (498674188771/1000000000000 : ℝ) (498674188779/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 4 (249337094407/500000000000 : ℝ) (249337094411/500000000000 : ℝ) (498674188771/1000000000000 : ℝ) (498674188779/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 5 (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 6 (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2021/16384 : ℝ))) 7 (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2021/16384 : ℝ)) hmem 8 (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2021/16384 : ℝ))) hcmem 8 (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2021/16384 : ℝ)) (124041860479/125000000000 : ℝ) (198466976767/200000000000 : ℝ) (62334273599/125000000000 : ℝ) (498674188801/1000000000000 : ℝ) (789366167391/1000000000000 : ℝ) (789366167409/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0116_exp_lower
  have heNumeric : (82197852879/40000000000 : ℝ)/4 ≤ Real.exp (-5328357073647/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82197852879/40000000000 : ℝ)/4 ≤ Real.exp ((4041/32768 : ℝ)-(789366167409/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4041/32768 : ℝ) (2021/16384 : ℝ) (789366167409/1000000000000 : ℝ) (82197852879/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0117; no trusted numerical premise.
theorem cover8_leaf0117_exp_radius : (998074004483661533/1000000000000000000 : ℝ) ≤ Real.exp ((-4043/262144 : ℝ)/8) ∧ Real.exp ((-4043/262144 : ℝ)/8) ≤ (499037002241830767/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4043/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0117_exp_lower : (7188405250087209/7812500000000000 : ℝ) ≤ Real.exp ((-2664181409011/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664181409011/4000000000000 : ℝ)/8) ≤ (920115872011162753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664181409011/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0117_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513736211607/250000000000 : ℝ) ≤ 4*Real.exp (2021/16384 : ℝ)*Real.exp (-mu (radius 8 (4043/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513736211607/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4043/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0117_exp_radius
  have hrNumeric : (246173875397/250000000000 : ℝ) ≤ Real.exp (-4043/262144 : ℝ) ∧ Real.exp (-4043/262144 : ℝ) ≤ (984695501589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246173875397/250000000000 : ℝ) ≤ (radius 8 (4043/32768 : ℝ)) ∧ (radius 8 (4043/32768 : ℝ)) ≤ (984695501589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4043/32768 : ℝ)) (246173875397/250000000000 : ℝ) (984695501589/1000000000000 : ℝ) (174283588299/1000000000000 : ℝ) (34856717661/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4043/32768 : ℝ)) (246173875397/250000000000 : ℝ) (984695501589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246173875397/250000000000 : ℝ) (984695501589/1000000000000 : ℝ) (496173875397/500000000000 : ℝ) (198469550159/200000000000 : ℝ) (496159123061/500000000000 : ℝ) (248079561531/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 1 (496173875397/500000000000 : ℝ) (198469550159/200000000000 : ℝ) (496159123061/500000000000 : ℝ) (248079561531/250000000000 : ℝ) (496166499229/500000000000 : ℝ) (49616649923/50000000000 : ℝ) (248083249587/250000000000 : ℝ) (19846659967/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 2 (496166499229/500000000000 : ℝ) (49616649923/50000000000 : ℝ) (248083249587/250000000000 : ℝ) (19846659967/20000000000 : ℝ) (992332998403/1000000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 3 (992332998403/1000000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 4 (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 5 (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 6 (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4043/32768 : ℝ)) 7 (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4043/32768 : ℝ))) (174283588299/1000000000000 : ℝ) (34856717661/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174283588299/1000000000000 : ℝ) (34856717661/200000000000 : ℝ) (587141794149/1000000000000 : ℝ) (587141794153/1000000000000 : ℝ) (104368214839/250000000000 : ℝ) (104368214841/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 1 (587141794149/1000000000000 : ℝ) (587141794153/1000000000000 : ℝ) (104368214839/250000000000 : ℝ) (104368214841/250000000000 : ℝ) (15697103961/31250000000 : ℝ) (502307326759/1000000000000 : ℝ) (247545835983/500000000000 : ℝ) (247545835987/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 2 (15697103961/31250000000 : ℝ) (502307326759/1000000000000 : ℝ) (247545835983/500000000000 : ℝ) (247545835987/500000000000 : ℝ) (498699499359/1000000000000 : ℝ) (498699499367/1000000000000 : ℝ) (19947457953/40000000000 : ℝ) (249343224417/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 3 (498699499359/1000000000000 : ℝ) (498699499367/1000000000000 : ℝ) (19947457953/40000000000 : ℝ) (249343224417/500000000000 : ℝ) (124673243523/250000000000 : ℝ) (498692974101/1000000000000 : ℝ) (498692974049/1000000000000 : ℝ) (249346487029/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 4 (124673243523/250000000000 : ℝ) (498692974101/1000000000000 : ℝ) (498692974049/1000000000000 : ℝ) (249346487029/500000000000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 5 (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 6 (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4043/32768 : ℝ))) 7 (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4043/32768 : ℝ)) hmem 8 (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4043/32768 : ℝ))) hcmem 8 (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4043/32768 : ℝ)) (496166499201/500000000000 : ℝ) (198466599681/200000000000 : ℝ) (49869297407/100000000000 : ℝ) (194801943/390625000 : ℝ) (157879480603/200000000000 : ℝ) (394698701517/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0117_exp_lower
  have heNumeric : (513736211607/250000000000 : ℝ)/4 ≤ Real.exp (-2664181409011/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513736211607/250000000000 : ℝ)/4 ≤ Real.exp ((2021/16384 : ℝ)-(394698701517/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2021/16384 : ℝ) (4043/32768 : ℝ) (394698701517/500000000000 : ℝ) (513736211607/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0118; no trusted numerical premise.
theorem cover8_leaf0118_exp_radius : (499036764282501513/500000000000000000 : ℝ) ≤ Real.exp ((-1011/65536 : ℝ)/8) ∧ Real.exp ((-1011/65536 : ℝ)/8) ≤ (998073528565003027/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1011/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0118_exp_lower : (920115790030351773/1000000000000000000 : ℝ) ≤ Real.exp ((-5328368520317/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328368520317/8000000000000 : ℝ)/8) ≤ (460057895015175887/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328368520317/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0118_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054943381691/1000000000000 : ℝ) ≤ 4*Real.exp (4043/32768 : ℝ)*Real.exp (-mu (radius 8 (1011/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054943381691/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1011/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0118_exp_radius
  have hrNumeric : (384645213/390625000 : ℝ) ≤ Real.exp (-1011/65536 : ℝ) ∧ Real.exp (-1011/65536 : ℝ) ≤ (984691745281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (384645213/390625000 : ℝ) ≤ (radius 8 (1011/8192 : ℝ)) ∧ (radius 8 (1011/8192 : ℝ)) ≤ (984691745281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1011/8192 : ℝ)) (384645213/390625000 : ℝ) (984691745281/1000000000000 : ℝ) (4357620249/25000000000 : ℝ) (174304809967/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1011/8192 : ℝ)) (384645213/390625000 : ℝ) (984691745281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (384645213/390625000 : ℝ) (984691745281/1000000000000 : ℝ) (775270213/781250000 : ℝ) (992345872641/1000000000000 : ℝ) (992316353427/1000000000000 : ℝ) (992316353429/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 1 (775270213/781250000 : ℝ) (992345872641/1000000000000 : ℝ) (992316353427/1000000000000 : ℝ) (992316353429/1000000000000 : ℝ) (992331113033/1000000000000 : ℝ) (198466222607/200000000000 : ℝ) (992331112923/1000000000000 : ℝ) (496165556463/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 2 (992331113033/1000000000000 : ℝ) (198466222607/200000000000 : ℝ) (992331112923/1000000000000 : ℝ) (496165556463/500000000000 : ℝ) (496165556489/500000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 3 (496165556489/500000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 4 (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 5 (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 6 (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1011/8192 : ℝ)) 7 (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1011/8192 : ℝ))) (4357620249/25000000000 : ℝ) (174304809967/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4357620249/25000000000 : ℝ) (174304809967/1000000000000 : ℝ) (29357620249/50000000000 : ℝ) (73394050623/125000000000 : ℝ) (417498275397/1000000000000 : ℝ) (417498275407/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 1 (29357620249/50000000000 : ℝ) (73394050623/125000000000 : ℝ) (417498275397/1000000000000 : ℝ) (417498275407/1000000000000 : ℝ) (125581335047/250000000000 : ℝ) (125581335049/250000000000 : ℝ) (495111216267/1000000000000 : ℝ) (123777804069/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 2 (125581335047/250000000000 : ℝ) (125581335049/250000000000 : ℝ) (495111216267/1000000000000 : ℝ) (123777804069/250000000000 : ℝ) (498718278227/1000000000000 : ℝ) (124679569559/250000000000 : ℝ) (249352616861/500000000000 : ℝ) (124676308433/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 3 (498718278227/1000000000000 : ℝ) (124679569559/250000000000 : ℝ) (249352616861/500000000000 : ℝ) (124676308433/250000000000 : ℝ) (249355877987/500000000000 : ℝ) (31169484749/62500000000 : ℝ) (498711755931/1000000000000 : ℝ) (249355877971/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 4 (249355877987/500000000000 : ℝ) (31169484749/62500000000 : ℝ) (498711755931/1000000000000 : ℝ) (249355877971/500000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 5 (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 6 (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1011/8192 : ℝ))) 7 (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1011/8192 : ℝ)) hmem 8 (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1011/8192 : ℝ))) hcmem 8 (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1011/8192 : ℝ)) (992331112977/1000000000000 : ℝ) (992331112981/1000000000000 : ℝ) (31169484747/62500000000 : ℝ) (498711755963/1000000000000 : ℝ) (789428633377/1000000000000 : ℝ) (789428633399/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0118_exp_lower
  have heNumeric : (2054943381691/1000000000000 : ℝ)/4 ≤ Real.exp (-5328368520317/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054943381691/1000000000000 : ℝ)/4 ≤ Real.exp ((4043/32768 : ℝ)-(789428633399/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4043/32768 : ℝ) (1011/8192 : ℝ) (789428633399/1000000000000 : ℝ) (2054943381691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0119; no trusted numerical premise.
theorem cover8_leaf0119_exp_radius : (15594891447602679/15625000000000000 : ℝ) ≤ Real.exp ((-4045/262144 : ℝ)/8) ∧ Real.exp ((-4045/262144 : ℝ)/8) ≤ (998073052646571457/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4045/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0119_exp_lower : (230028927163573537/250000000000000000 : ℝ) ≤ Real.exp ((-1332093545137/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332093545137/2000000000000 : ℝ)/8) ≤ (920115708654294149/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332093545137/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0119_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686774097/12500000000 : ℝ) ≤ 4*Real.exp (1011/8192 : ℝ)*Real.exp (-mu (radius 8 (4045/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (25686774097/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4045/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0119_exp_radius
  have hrNumeric : (984687988987/1000000000000 : ℝ) ≤ Real.exp (-4045/262144 : ℝ) ∧ Real.exp (-4045/262144 : ℝ) ≤ (246171997247/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984687988987/1000000000000 : ℝ) ≤ (radius 8 (4045/32768 : ℝ)) ∧ (radius 8 (4045/32768 : ℝ)) ≤ (246171997247/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4045/32768 : ℝ)) (984687988987/1000000000000 : ℝ) (246171997247/250000000000 : ℝ) (174326028873/1000000000000 : ℝ) (2179075361/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4045/32768 : ℝ)) (984687988987/1000000000000 : ℝ) (246171997247/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984687988987/1000000000000 : ℝ) (246171997247/250000000000 : ℝ) (992343994493/1000000000000 : ℝ) (496171997247/500000000000 : ℝ) (15504913449/15625000000 : ℝ) (496157230369/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 1 (992343994493/1000000000000 : ℝ) (496171997247/500000000000 : ℝ) (15504913449/15625000000 : ℝ) (496157230369/500000000000 : ℝ) (496164613807/500000000000 : ℝ) (31010288363/31250000000 : ℝ) (62020576719/62500000000 : ℝ) (992329227507/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 2 (496164613807/500000000000 : ℝ) (31010288363/31250000000 : ℝ) (62020576719/62500000000 : ℝ) (992329227507/1000000000000 : ℝ) (992329227559/1000000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 3 (992329227559/1000000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 4 (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 5 (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 6 (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4045/32768 : ℝ)) 7 (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4045/32768 : ℝ))) (174326028873/1000000000000 : ℝ) (2179075361/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174326028873/1000000000000 : ℝ) (2179075361/12500000000 : ℝ) (146790753609/250000000000 : ℝ) (14679075361/25000000000 : ℝ) (417523686601/1000000000000 : ℝ) (41752368661/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 1 (146790753609/250000000000 : ℝ) (14679075361/25000000000 : ℝ) (417523686601/1000000000000 : ℝ) (41752368661/100000000000 : ℝ) (251171675259/500000000000 : ℝ) (20093734021/40000000000 : ℝ) (247565378447/500000000000 : ℝ) (247565378451/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 2 (251171675259/500000000000 : ℝ) (20093734021/40000000000 : ℝ) (247565378447/500000000000 : ℝ) (247565378451/500000000000 : ℝ) (249368526853/500000000000 : ℝ) (249368526857/500000000000 : ℝ) (19948960609/40000000000 : ℝ) (249362007617/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 3 (249368526853/500000000000 : ℝ) (249368526857/500000000000 : ℝ) (19948960609/40000000000 : ℝ) (249362007617/500000000000 : ℝ) (99746106893/200000000000 : ℝ) (249365267237/500000000000 : ℝ) (249365267211/500000000000 : ℝ) (15585329201/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 4 (99746106893/200000000000 : ℝ) (249365267237/500000000000 : ℝ) (249365267211/500000000000 : ℝ) (15585329201/31250000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 5 (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 6 (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4045/32768 : ℝ))) 7 (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4045/32768 : ℝ)) hmem 8 (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4045/32768 : ℝ))) hcmem 8 (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4045/32768 : ℝ)) (496164613779/500000000000 : ℝ) (496164613781/500000000000 : ℝ) (498730534443/1000000000000 : ℝ) (498730534453/1000000000000 : ℝ) (394729929243/500000000000 : ℝ) (394729929253/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0119_exp_lower
  have heNumeric : (25686774097/12500000000 : ℝ)/4 ≤ Real.exp (-1332093545137/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686774097/12500000000 : ℝ)/4 ≤ Real.exp ((1011/8192 : ℝ)-(394729929253/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1011/8192 : ℝ) (4045/32768 : ℝ) (394729929253/500000000000 : ℝ) (25686774097/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0120; no trusted numerical premise.
theorem cover8_leaf0120_exp_radius : (49903628836418341/50000000000000000 : ℝ) ≤ Real.exp ((-2023/131072 : ℝ)/8) ∧ Real.exp ((-2023/131072 : ℝ)/8) ≤ (998072576728366821/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2023/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0120_exp_lower : (920115627880689427/1000000000000000000 : ℝ) ≤ Real.exp ((-42627038391/64000000000 : ℝ)/8) ∧ Real.exp ((-42627038391/64000000000 : ℝ)/8) ≤ (230028906970172357/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42627038391/64000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0120_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054940484593/1000000000000 : ℝ) ≤ 4*Real.exp (4045/32768 : ℝ)*Real.exp (-mu (radius 8 (2023/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054940484593/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2023/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0120_exp_radius
  have hrNumeric : (984684232707/1000000000000 : ℝ) ≤ Real.exp (-2023/131072 : ℝ) ∧ Real.exp (-2023/131072 : ℝ) ≤ (246171058177/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984684232707/1000000000000 : ℝ) ≤ (radius 8 (2023/16384 : ℝ)) ∧ (radius 8 (2023/16384 : ℝ)) ≤ (246171058177/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2023/16384 : ℝ)) (984684232707/1000000000000 : ℝ) (246171058177/250000000000 : ℝ) (174347245049/1000000000000 : ℝ) (34869449011/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2023/16384 : ℝ)) (984684232707/1000000000000 : ℝ) (246171058177/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984684232707/1000000000000 : ℝ) (246171058177/250000000000 : ℝ) (992342116353/1000000000000 : ℝ) (496171058177/500000000000 : ℝ) (62019535503/62500000000 : ℝ) (992312568049/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 1 (992342116353/1000000000000 : ℝ) (496171058177/500000000000 : ℝ) (62019535503/62500000000 : ℝ) (992312568049/1000000000000 : ℝ) (4961636711/5000000000 : ℝ) (496163671101/500000000000 : ℝ) (99232734209/100000000000 : ℝ) (248081835523/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 2 (4961636711/5000000000 : ℝ) (496163671101/500000000000 : ℝ) (99232734209/100000000000 : ℝ) (248081835523/250000000000 : ℝ) (198465468429/200000000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 3 (198465468429/200000000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 4 (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 5 (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 6 (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2023/16384 : ℝ)) 7 (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2023/16384 : ℝ))) (174347245049/1000000000000 : ℝ) (34869449011/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174347245049/1000000000000 : ℝ) (34869449011/200000000000 : ℝ) (146793405631/250000000000 : ℝ) (2293646963/3906250000 : ℝ) (20877454649/50000000000 : ℝ) (104387273247/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 1 (146793405631/250000000000 : ℝ) (2293646963/3906250000 : ℝ) (20877454649/50000000000 : ℝ) (104387273247/250000000000 : ℝ) (62795169719/125000000000 : ℝ) (251180678879/500000000000 : ℝ) (495150293857/1000000000000 : ℝ) (61893786733/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 2 (62795169719/125000000000 : ℝ) (251180678879/500000000000 : ℝ) (495150293857/1000000000000 : ℝ) (61893786733/125000000000 : ℝ) (124688956451/250000000000 : ℝ) (498755825811/1000000000000 : ℝ) (3896428073/7812500000 : ℝ) (62342849169/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 3 (124688956451/250000000000 : ℝ) (498755825811/1000000000000 : ℝ) (3896428073/7812500000 : ℝ) (62342849169/125000000000 : ℝ) (249374654787/500000000000 : ℝ) (249374654791/500000000000 : ℝ) (498749309531/1000000000000 : ℝ) (498749309539/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 4 (249374654787/500000000000 : ℝ) (249374654791/500000000000 : ℝ) (498749309531/1000000000000 : ℝ) (498749309539/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 5 (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 6 (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2023/16384 : ℝ))) 7 (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2023/16384 : ℝ)) hmem 8 (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2023/16384 : ℝ))) hcmem 8 (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2023/16384 : ℝ)) (15505114721/15625000000 : ℝ) (992327342147/1000000000000 : ℝ) (31171831847/62500000000 : ℝ) (498749309561/1000000000000 : ℝ) (394745539179/500000000000 : ℝ) (6315928627/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0120_exp_lower
  have heNumeric : (2054940484593/1000000000000 : ℝ)/4 ≤ Real.exp (-42627038391/64000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054940484593/1000000000000 : ℝ)/4 ≤ Real.exp ((4045/32768 : ℝ)-(6315928627/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4045/32768 : ℝ) (2023/16384 : ℝ) (6315928627/8000000000 : ℝ) (2054940484593/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0121; no trusted numerical premise.
theorem cover8_leaf0121_exp_radius : (1559487657516233/1562500000000000 : ℝ) ≤ Real.exp ((-4047/262144 : ℝ)/8) ∧ Real.exp ((-4047/262144 : ℝ)/8) ≤ (998072100810389121/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4047/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0121_exp_lower : (920115547711147653/1000000000000000000 : ℝ) ≤ Real.exp ((-2664192687593/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664192687593/4000000000000 : ℝ)/8) ≤ (460057773855573827/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664192687593/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0121_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102746952611/50000000000 : ℝ) ≤ 4*Real.exp (2023/16384 : ℝ)*Real.exp (-mu (radius 8 (4047/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102746952611/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4047/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0121_exp_radius
  have hrNumeric : (492340238221/500000000000 : ℝ) ≤ Real.exp (-4047/262144 : ℝ) ∧ Real.exp (-4047/262144 : ℝ) ≤ (984680476443/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492340238221/500000000000 : ℝ) ≤ (radius 8 (4047/32768 : ℝ)) ∧ (radius 8 (4047/32768 : ℝ)) ≤ (984680476443/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4047/32768 : ℝ)) (492340238221/500000000000 : ℝ) (984680476443/1000000000000 : ℝ) (174368458477/1000000000000 : ℝ) (43592114621/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4047/32768 : ℝ)) (492340238221/500000000000 : ℝ) (984680476443/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492340238221/500000000000 : ℝ) (984680476443/1000000000000 : ℝ) (992340238221/1000000000000 : ℝ) (496170119111/500000000000 : ℝ) (248077668841/250000000000 : ℝ) (198462135073/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 1 (992340238221/1000000000000 : ℝ) (496170119111/500000000000 : ℝ) (248077668841/250000000000 : ℝ) (198462135073/200000000000 : ℝ) (124040682099/125000000000 : ℝ) (496162728397/500000000000 : ℝ) (496162728341/500000000000 : ℝ) (248081364171/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 2 (124040682099/125000000000 : ℝ) (496162728397/500000000000 : ℝ) (496162728341/500000000000 : ℝ) (248081364171/250000000000 : ℝ) (992325456737/1000000000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 3 (992325456737/1000000000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 4 (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 5 (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 6 (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4047/32768 : ℝ)) 7 (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4047/32768 : ℝ))) (174368458477/1000000000000 : ℝ) (43592114621/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174368458477/1000000000000 : ℝ) (43592114621/250000000000 : ℝ) (293592114619/500000000000 : ℝ) (293592114621/500000000000 : ℝ) (104393623631/250000000000 : ℝ) (417574494533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 1 (293592114619/500000000000 : ℝ) (293592114621/500000000000 : ℝ) (104393623631/250000000000 : ℝ) (417574494533/1000000000000 : ℝ) (502379361881/1000000000000 : ℝ) (15699355059/31250000000 : ℝ) (247584913573/500000000000 : ℝ) (247584913577/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 2 (502379361881/1000000000000 : ℝ) (15699355059/31250000000 : ℝ) (247584913573/500000000000 : ℝ) (247584913577/500000000000 : ℝ) (498774594513/1000000000000 : ℝ) (498774594521/1000000000000 : ℝ) (49876156807/100000000000 : ℝ) (498761568079/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 3 (498774594513/1000000000000 : ℝ) (498774594521/1000000000000 : ℝ) (49876156807/100000000000 : ℝ) (498761568079/1000000000000 : ℝ) (498768081291/1000000000000 : ℝ) (4987680813/10000000000 : ℝ) (15586502539/31250000000 : ℝ) (249384040629/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 4 (498768081291/1000000000000 : ℝ) (4987680813/10000000000 : ℝ) (15586502539/31250000000 : ℝ) (249384040629/500000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 5 (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 6 (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4047/32768 : ℝ))) 7 (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4047/32768 : ℝ)) hmem 8 (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4047/32768 : ℝ))) hcmem 8 (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4047/32768 : ℝ)) (31010170523/31250000000 : ℝ) (992325456739/1000000000000 : ℝ) (498768081269/1000000000000 : ℝ) (498768081279/1000000000000 : ℝ) (197380573243/250000000000 : ℝ) (3084071457/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0121_exp_lower
  have heNumeric : (102746952611/50000000000 : ℝ)/4 ≤ Real.exp (-2664192687593/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102746952611/50000000000 : ℝ)/4 ≤ Real.exp ((2023/16384 : ℝ)-(3084071457/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2023/16384 : ℝ) (4047/32768 : ℝ) (3084071457/3906250000 : ℝ) (102746952611/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0122; no trusted numerical premise.
theorem cover8_leaf0122_exp_radius : (249517906223159589/250000000000000000 : ℝ) ≤ Real.exp ((-253/16384 : ℝ)/8) ∧ Real.exp ((-253/16384 : ℝ)/8) ≤ (998071624892638357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-253/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0122_exp_lower : (46005773407231677/50000000000000000 : ℝ) ≤ Real.exp ((-5328390909553/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328390909553/8000000000000 : ℝ)/8) ≤ (920115468144633541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328390909553/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0122_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027468815311/500000000000 : ℝ) ≤ 4*Real.exp (4047/32768 : ℝ)*Real.exp (-mu (radius 8 (253/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027468815311/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (253/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0122_exp_radius
  have hrNumeric : (984676720191/1000000000000 : ℝ) ≤ Real.exp (-253/16384 : ℝ) ∧ Real.exp (-253/16384 : ℝ) ≤ (15385573753/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984676720191/1000000000000 : ℝ) ≤ (radius 8 (253/2048 : ℝ)) ∧ (radius 8 (253/2048 : ℝ)) ≤ (15385573753/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (253/2048 : ℝ)) (984676720191/1000000000000 : ℝ) (15385573753/15625000000 : ℝ) (87194834583/500000000000 : ℝ) (43597417293/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (253/2048 : ℝ)) (984676720191/1000000000000 : ℝ) (15385573753/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (253/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984676720191/1000000000000 : ℝ) (15385573753/15625000000 : ℝ) (198467672019/200000000000 : ℝ) (31010573753/31250000000 : ℝ) (992308782683/1000000000000 : ℝ) (198461756537/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (253/2048 : ℝ)) 1 (198467672019/200000000000 : ℝ) (31010573753/31250000000 : ℝ) (992308782683/1000000000000 : ℝ) (198461756537/200000000000 : ℝ) (992323571389/1000000000000 : ℝ) (992323571391/1000000000000 : ℝ) (496161785639/500000000000 : ℝ) (992323571281/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (253/2048 : ℝ)) 2 (992323571389/1000000000000 : ℝ) (992323571391/1000000000000 : ℝ) (496161785639/500000000000 : ℝ) (992323571281/1000000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (253/2048 : ℝ)) 3 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (253/2048 : ℝ)) 4 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (253/2048 : ℝ)) 5 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (253/2048 : ℝ)) 6 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (253/2048 : ℝ)) 7 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (253/2048 : ℝ))) (87194834583/500000000000 : ℝ) (43597417293/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87194834583/500000000000 : ℝ) (43597417293/250000000000 : ℝ) (587194834583/1000000000000 : ℝ) (293597417293/500000000000 : ℝ) (208799945621/500000000000 : ℝ) (334079913/800000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 1 (587194834583/1000000000000 : ℝ) (293597417293/500000000000 : ℝ) (208799945621/500000000000 : ℝ) (334079913/800000000 : ℝ) (15699917591/31250000000 : ℝ) (251198681459/500000000000 : ℝ) (495189356771/1000000000000 : ℝ) (247594678389/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 2 (15699917591/31250000000 : ℝ) (251198681459/500000000000 : ℝ) (495189356771/1000000000000 : ℝ) (247594678389/500000000000 : ℝ) (498793359841/1000000000000 : ℝ) (62349169981/125000000000 : ℝ) (498780339411/1000000000000 : ℝ) (498780339419/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 3 (498793359841/1000000000000 : ℝ) (62349169981/125000000000 : ℝ) (498780339411/1000000000000 : ℝ) (498780339419/1000000000000 : ℝ) (249393424813/500000000000 : ℝ) (249393424817/500000000000 : ℝ) (498786849583/1000000000000 : ℝ) (62348356199/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 4 (249393424813/500000000000 : ℝ) (249393424817/500000000000 : ℝ) (498786849583/1000000000000 : ℝ) (62348356199/125000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 5 (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 6 (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (253/2048 : ℝ))) 7 (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (253/2048 : ℝ)) hmem 8 (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (253/2048 : ℝ))) hcmem 8 (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (253/2048 : ℝ)) (992323571333/1000000000000 : ℝ) (124040446417/125000000000 : ℝ) (124696712401/250000000000 : ℝ) (498786849613/1000000000000 : ℝ) (197388375587/250000000000 : ℝ) (394776751183/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0122_exp_lower
  have heNumeric : (1027468815311/500000000000 : ℝ)/4 ≤ Real.exp (-5328390909553/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027468815311/500000000000 : ℝ)/4 ≤ Real.exp ((4047/32768 : ℝ)-(394776751183/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4047/32768 : ℝ) (253/2048 : ℝ) (394776751183/500000000000 : ℝ) (1027468815311/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0123; no trusted numerical premise.
theorem cover8_leaf0123_exp_radius : (499035574487557263/500000000000000000 : ℝ) ≤ Real.exp ((-4049/262144 : ℝ)/8) ∧ Real.exp ((-4049/262144 : ℝ)/8) ≤ (998071148975114527/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4049/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0123_exp_lower : (230028847295401747/250000000000000000 : ℝ) ≤ Real.exp ((-666049550243/1000000000000 : ℝ)/8) ∧ Real.exp ((-666049550243/1000000000000 : ℝ)/8) ≤ (920115389181606989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666049550243/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0123_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64216756869/31250000000 : ℝ) ≤ 4*Real.exp (253/2048 : ℝ)*Real.exp (-mu (radius 8 (4049/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (64216756869/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4049/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0123_exp_radius
  have hrNumeric : (196934592791/200000000000 : ℝ) ≤ Real.exp (-4049/262144 : ℝ) ∧ Real.exp (-4049/262144 : ℝ) ≤ (246168240989/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196934592791/200000000000 : ℝ) ≤ (radius 8 (4049/32768 : ℝ)) ∧ (radius 8 (4049/32768 : ℝ)) ≤ (246168240989/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4049/32768 : ℝ)) (196934592791/200000000000 : ℝ) (246168240989/250000000000 : ℝ) (174410877109/1000000000000 : ℝ) (43602719279/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4049/32768 : ℝ)) (196934592791/200000000000 : ℝ) (246168240989/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196934592791/200000000000 : ℝ) (246168240989/250000000000 : ℝ) (992336481977/1000000000000 : ℝ) (496168240989/500000000000 : ℝ) (496153445003/500000000000 : ℝ) (124038361251/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 1 (992336481977/1000000000000 : ℝ) (496168240989/500000000000 : ℝ) (496153445003/500000000000 : ℝ) (124038361251/125000000000 : ℝ) (992321685991/1000000000000 : ℝ) (992321685993/1000000000000 : ℝ) (992321685881/1000000000000 : ℝ) (992321685883/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 2 (992321685991/1000000000000 : ℝ) (992321685993/1000000000000 : ℝ) (992321685881/1000000000000 : ℝ) (992321685883/1000000000000 : ℝ) (62020105371/62500000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 3 (62020105371/62500000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 4 (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 5 (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 6 (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4049/32768 : ℝ)) 7 (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4049/32768 : ℝ))) (174410877109/1000000000000 : ℝ) (43602719279/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174410877109/1000000000000 : ℝ) (43602719279/250000000000 : ℝ) (293602719277/500000000000 : ℝ) (293602719279/500000000000 : ℝ) (417625283129/1000000000000 : ℝ) (208812641569/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 1 (293602719277/500000000000 : ℝ) (293602719279/500000000000 : ℝ) (417625283129/1000000000000 : ℝ) (208812641569/500000000000 : ℝ) (502415360841/1000000000000 : ℝ) (31400960053/62500000000 : ℝ) (247604441363/500000000000 : ℝ) (247604441367/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 2 (502415360841/1000000000000 : ℝ) (31400960053/62500000000 : ℝ) (247604441363/500000000000 : ℝ) (247604441367/500000000000 : ℝ) (498812121783/1000000000000 : ℝ) (498812121791/1000000000000 : ℝ) (498799107363/1000000000000 : ℝ) (498799107371/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 3 (498812121783/1000000000000 : ℝ) (498812121791/1000000000000 : ℝ) (498799107363/1000000000000 : ℝ) (498799107371/1000000000000 : ℝ) (498805614573/1000000000000 : ℝ) (498805614581/1000000000000 : ℝ) (49880561453/100000000000 : ℝ) (498805614539/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 4 (498805614573/1000000000000 : ℝ) (498805614581/1000000000000 : ℝ) (49880561453/100000000000 : ℝ) (498805614539/1000000000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 5 (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 6 (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4049/32768 : ℝ))) 7 (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4049/32768 : ℝ)) hmem 8 (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4049/32768 : ℝ))) hcmem 8 (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4049/32768 : ℝ)) (198464337187/200000000000 : ℝ) (496160842969/500000000000 : ℝ) (498805614551/1000000000000 : ℝ) (3117535091/6250000000 : ℝ) (197396176619/250000000000 : ℝ) (789584706493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0123_exp_lower
  have heNumeric : (64216756869/31250000000 : ℝ)/4 ≤ Real.exp (-666049550243/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64216756869/31250000000 : ℝ)/4 ≤ Real.exp ((253/2048 : ℝ)-(789584706493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (253/2048 : ℝ) (4049/32768 : ℝ) (789584706493/1000000000000 : ℝ) (64216756869/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0124; no trusted numerical premise.
theorem cover8_leaf0124_exp_radius : (31189708533056801/31250000000000000 : ℝ) ≤ Real.exp ((-2025/131072 : ℝ)/8) ∧ Real.exp ((-2025/131072 : ℝ)/8) ≤ (998070673057817633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2025/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0124_exp_lower : (920115310820917697/1000000000000000000 : ℝ) ≤ Real.exp ((-5328401852439/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328401852439/8000000000000 : ℝ)/8) ≤ (460057655410458849/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328401852439/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0124_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513733704939/250000000000 : ℝ) ≤ 4*Real.exp (4049/32768 : ℝ)*Real.exp (-mu (radius 8 (2025/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513733704939/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2025/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0124_exp_radius
  have hrNumeric : (984669207733/1000000000000 : ℝ) ≤ Real.exp (-2025/131072 : ℝ) ∧ Real.exp (-2025/131072 : ℝ) ≤ (492334603867/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984669207733/1000000000000 : ℝ) ≤ (radius 8 (2025/16384 : ℝ)) ∧ (radius 8 (2025/16384 : ℝ)) ≤ (492334603867/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2025/16384 : ℝ)) (984669207733/1000000000000 : ℝ) (492334603867/500000000000 : ℝ) (87216041157/500000000000 : ℝ) (2180401029/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2025/16384 : ℝ)) (984669207733/1000000000000 : ℝ) (492334603867/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984669207733/1000000000000 : ℝ) (492334603867/500000000000 : ℝ) (496167301933/500000000000 : ℝ) (992334603867/1000000000000 : ℝ) (992304997333/1000000000000 : ℝ) (496152498667/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 1 (496167301933/500000000000 : ℝ) (992334603867/1000000000000 : ℝ) (992304997333/1000000000000 : ℝ) (496152498667/500000000000 : ℝ) (992319800599/1000000000000 : ℝ) (992319800601/1000000000000 : ℝ) (992319800489/1000000000000 : ℝ) (992319800491/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 2 (992319800599/1000000000000 : ℝ) (992319800601/1000000000000 : ℝ) (992319800489/1000000000000 : ℝ) (992319800491/1000000000000 : ℝ) (31009993767/31250000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 3 (31009993767/31250000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 4 (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 5 (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 6 (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2025/16384 : ℝ)) 7 (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2025/16384 : ℝ))) (87216041157/500000000000 : ℝ) (2180401029/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87216041157/500000000000 : ℝ) (2180401029/12500000000 : ℝ) (587216041157/1000000000000 : ℝ) (14680401029/25000000000 : ℝ) (208825335097/500000000000 : ℝ) (208825335101/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 1 (587216041157/1000000000000 : ℝ) (14680401029/25000000000 : ℝ) (208825335097/500000000000 : ℝ) (208825335101/500000000000 : ℝ) (20097334227/40000000000 : ℝ) (502433355681/1000000000000 : ℝ) (495228405019/1000000000000 : ℝ) (247614202513/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 2 (20097334227/40000000000 : ℝ) (502433355681/1000000000000 : ℝ) (495228405019/1000000000000 : ℝ) (247614202513/500000000000 : ℝ) (498830880347/1000000000000 : ℝ) (249415440177/500000000000 : ℝ) (124704467983/250000000000 : ℝ) (24940893597/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 3 (498830880347/1000000000000 : ℝ) (249415440177/500000000000 : ℝ) (124704467983/250000000000 : ℝ) (24940893597/50000000000 : ℝ) (498824376139/1000000000000 : ℝ) (498824376147/1000000000000 : ℝ) (498824376097/1000000000000 : ℝ) (99764875221/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 4 (498824376139/1000000000000 : ℝ) (498824376147/1000000000000 : ℝ) (498824376097/1000000000000 : ℝ) (99764875221/200000000000 : ℝ) (249412188059/500000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 5 (249412188059/500000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 6 (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2025/16384 : ℝ))) 7 (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2025/16384 : ℝ)) hmem 8 (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2025/16384 : ℝ))) hcmem 8 (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2025/16384 : ℝ)) (992319800543/1000000000000 : ℝ) (496159900273/500000000000 : ℝ) (498824376117/1000000000000 : ℝ) (249412188063/500000000000 : ℝ) (157923181073/200000000000 : ℝ) (789615905383/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0124_exp_lower
  have heNumeric : (513733704939/250000000000 : ℝ)/4 ≤ Real.exp (-5328401852439/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513733704939/250000000000 : ℝ)/4 ≤ Real.exp ((4049/32768 : ℝ)-(789615905383/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4049/32768 : ℝ) (2025/16384 : ℝ) (789615905383/1000000000000 : ℝ) (513733704939/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0100_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0100_certificate
#check SmaleRate.Proofs.cover8_leaf0101_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0101_certificate
#check SmaleRate.Proofs.cover8_leaf0102_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0102_certificate
#check SmaleRate.Proofs.cover8_leaf0103_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0103_certificate
#check SmaleRate.Proofs.cover8_leaf0104_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0104_certificate
#check SmaleRate.Proofs.cover8_leaf0105_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0105_certificate
#check SmaleRate.Proofs.cover8_leaf0106_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0106_certificate
#check SmaleRate.Proofs.cover8_leaf0107_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0107_certificate
#check SmaleRate.Proofs.cover8_leaf0108_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0108_certificate
#check SmaleRate.Proofs.cover8_leaf0109_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0109_certificate
#check SmaleRate.Proofs.cover8_leaf0110_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0110_certificate
#check SmaleRate.Proofs.cover8_leaf0111_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0111_certificate
#check SmaleRate.Proofs.cover8_leaf0112_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0112_certificate
#check SmaleRate.Proofs.cover8_leaf0113_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0113_certificate
#check SmaleRate.Proofs.cover8_leaf0114_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0114_certificate
#check SmaleRate.Proofs.cover8_leaf0115_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0115_certificate
#check SmaleRate.Proofs.cover8_leaf0116_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0116_certificate
#check SmaleRate.Proofs.cover8_leaf0117_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0117_certificate
#check SmaleRate.Proofs.cover8_leaf0118_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0118_certificate
#check SmaleRate.Proofs.cover8_leaf0119_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0119_certificate
#check SmaleRate.Proofs.cover8_leaf0120_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0120_certificate
#check SmaleRate.Proofs.cover8_leaf0121_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0121_certificate
#check SmaleRate.Proofs.cover8_leaf0122_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0122_certificate
#check SmaleRate.Proofs.cover8_leaf0123_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0123_certificate
#check SmaleRate.Proofs.cover8_leaf0124_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0124_certificate
