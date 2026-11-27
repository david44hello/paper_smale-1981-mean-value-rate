/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0425; no trusted numerical premise.
theorem cover7_leaf0425_exp_radius : (99754091391155369/100000000000000000 : ℝ) ≤ Real.exp ((-2259/114688 : ℝ)/8) ∧ Real.exp ((-2259/114688 : ℝ)/8) ≤ (997540913911553691/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2259/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0425_exp_lower : (183617958827423301/200000000000000000 : ℝ) ≤ Real.exp ((-10938890007173/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938890007173/16000000000000 : ℝ)/8) ≤ (459044897068558253/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938890007173/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0425_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023009343/1000000000000 : ℝ) ≤ 4*Real.exp (9035/65536 : ℝ)*Real.exp (-mu (radius 7 (2259/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023009343/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2259/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0425_exp_radius
  have hrNumeric : (98049580003/100000000000 : ℝ) ≤ Real.exp (-2259/114688 : ℝ) ∧ Real.exp (-2259/114688 : ℝ) ≤ (980495800031/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98049580003/100000000000 : ℝ) ≤ (radius 7 (2259/16384 : ℝ)) ∧ (radius 7 (2259/16384 : ℝ)) ≤ (980495800031/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2259/16384 : ℝ)) (98049580003/100000000000 : ℝ) (980495800031/1000000000000 : ℝ) (196540036943/1000000000000 : ℝ) (196540036949/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2259/16384 : ℝ)) (98049580003/100000000000 : ℝ) (980495800031/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98049580003/100000000000 : ℝ) (980495800031/1000000000000 : ℝ) (198049580003/200000000000 : ℝ) (61890493751/62500000000 : ℝ) (990199878827/1000000000000 : ℝ) (990199878829/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 1 (198049580003/200000000000 : ℝ) (61890493751/62500000000 : ℝ) (990199878827/1000000000000 : ℝ) (990199878829/1000000000000 : ℝ) (990223889421/1000000000000 : ℝ) (990223889423/1000000000000 : ℝ) (990223889129/1000000000000 : ℝ) (247555972283/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 2 (990223889421/1000000000000 : ℝ) (990223889423/1000000000000 : ℝ) (990223889129/1000000000000 : ℝ) (247555972283/250000000000 : ℝ) (39608955571/40000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 3 (39608955571/40000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 4 (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 5 (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 6 (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2259/16384 : ℝ)) 7 (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2259/16384 : ℝ))) (196540036943/1000000000000 : ℝ) (196540036949/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196540036943/1000000000000 : ℝ) (196540036949/1000000000000 : ℝ) (598270018471/1000000000000 : ℝ) (23930800739/40000000000 : ℝ) (443328362439/1000000000000 : ℝ) (221664181223/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 1 (598270018471/1000000000000 : ℝ) (23930800739/40000000000 : ℝ) (443328362439/1000000000000 : ℝ) (221664181223/500000000000 : ℝ) (104159838091/200000000000 : ℝ) (520799190461/1000000000000 : ℝ) (257502459981/500000000000 : ℝ) (16093903749/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 2 (104159838091/200000000000 : ℝ) (520799190461/1000000000000 : ℝ) (257502459981/500000000000 : ℝ) (16093903749/31250000000 : ℝ) (64737756901/125000000000 : ℝ) (103580411043/200000000000 : ℝ) (258946975941/500000000000 : ℝ) (517893951889/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 3 (64737756901/125000000000 : ℝ) (103580411043/200000000000 : ℝ) (258946975941/500000000000 : ℝ) (517893951889/1000000000000 : ℝ) (103579600709/200000000000 : ℝ) (16184312611/31250000000 : ℝ) (517898003529/1000000000000 : ℝ) (517898003537/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 4 (103579600709/200000000000 : ℝ) (16184312611/31250000000 : ℝ) (517898003529/1000000000000 : ℝ) (517898003537/1000000000000 : ℝ) (517898003537/1000000000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 5 (517898003537/1000000000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 6 (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2259/16384 : ℝ))) 7 (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2259/16384 : ℝ)) hmem 8 (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2259/16384 : ℝ))) hcmem 8 (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2259/16384 : ℝ)) (495111944637/500000000000 : ℝ) (495111944639/500000000000 : ℝ) (32368625221/62500000000 : ℝ) (103579600709/200000000000 : ℝ) (82154378461/100000000000 : ℝ) (205385946157/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0425_exp_lower
  have heNumeric : (2019023009343/1000000000000 : ℝ)/4 ≤ Real.exp (-10938890007173/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023009343/1000000000000 : ℝ)/4 ≤ Real.exp ((9035/65536 : ℝ)-(205385946157/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9035/65536 : ℝ) (2259/16384 : ℝ) (205385946157/250000000000 : ℝ) (2019023009343/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0426; no trusted numerical premise.
theorem cover7_leaf0426_exp_radius : (997540642103262389/1000000000000000000 : ℝ) ≤ Real.exp ((-1291/65536 : ℝ)/8) ∧ Real.exp ((-1291/65536 : ℝ)/8) ≤ (99754064210326239/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1291/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0426_exp_lower : (114761226037920509/125000000000000000 : ℝ) ≤ Real.exp ((-2734722008029/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734722008029/4000000000000 : ℝ)/8) ≤ (918089808303364073/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734722008029/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0426_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023258573/1000000000000 : ℝ) ≤ 4*Real.exp (2259/16384 : ℝ)*Real.exp (-mu (radius 7 (9037/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023258573/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9037/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0426_exp_radius
  have hrNumeric : (980493662721/1000000000000 : ℝ) ≤ Real.exp (-1291/65536 : ℝ) ∧ Real.exp (-1291/65536 : ℝ) ≤ (490246831361/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980493662721/1000000000000 : ℝ) ≤ (radius 7 (9037/65536 : ℝ)) ∧ (radius 7 (9037/65536 : ℝ)) ≤ (490246831361/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9037/65536 : ℝ)) (980493662721/1000000000000 : ℝ) (490246831361/500000000000 : ℝ) (39310139843/200000000000 : ℝ) (196550699221/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9037/65536 : ℝ)) (980493662721/1000000000000 : ℝ) (490246831361/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980493662721/1000000000000 : ℝ) (490246831361/500000000000 : ℝ) (773630337/781250000 : ℝ) (990246831361/1000000000000 : ℝ) (198039759919/200000000000 : ℝ) (990198799597/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 1 (773630337/781250000 : ℝ) (990246831361/1000000000000 : ℝ) (198039759919/200000000000 : ℝ) (990198799597/1000000000000 : ℝ) (990222815477/1000000000000 : ℝ) (990222815479/1000000000000 : ℝ) (495111407593/500000000000 : ℝ) (247555703797/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 2 (990222815477/1000000000000 : ℝ) (990222815479/1000000000000 : ℝ) (495111407593/500000000000 : ℝ) (247555703797/250000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 3 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 4 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 5 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 6 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9037/65536 : ℝ)) 7 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9037/65536 : ℝ))) (39310139843/200000000000 : ℝ) (196550699221/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39310139843/200000000000 : ℝ) (196550699221/1000000000000 : ℝ) (598275349607/1000000000000 : ℝ) (598275349611/1000000000000 : ℝ) (443340387529/1000000000000 : ℝ) (443340387537/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 1 (598275349607/1000000000000 : ℝ) (598275349611/1000000000000 : ℝ) (443340387529/1000000000000 : ℝ) (443340387537/1000000000000 : ℝ) (65100983571/125000000000 : ℝ) (260403934287/500000000000 : ℝ) (515014199167/1000000000000 : ℝ) (257507099587/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 2 (65100983571/125000000000 : ℝ) (260403934287/500000000000 : ℝ) (515014199167/1000000000000 : ℝ) (257507099587/500000000000 : ℝ) (517911033867/1000000000000 : ℝ) (258955516937/500000000000 : ℝ) (517902932363/1000000000000 : ℝ) (51790293237/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 3 (517911033867/1000000000000 : ℝ) (258955516937/500000000000 : ℝ) (517902932363/1000000000000 : ℝ) (51790293237/100000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491561/500000000000 : ℝ) (517906983099/1000000000000 : ℝ) (517906983107/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 4 (103581396623/200000000000 : ℝ) (258953491561/500000000000 : ℝ) (517906983099/1000000000000 : ℝ) (517906983107/1000000000000 : ℝ) (517906983107/1000000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 5 (517906983107/1000000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 6 (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9037/65536 : ℝ))) 7 (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9037/65536 : ℝ)) hmem 8 (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9037/65536 : ℝ))) hcmem 8 (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9037/65536 : ℝ)) (990222815331/1000000000000 : ℝ) (495111407667/500000000000 : ℝ) (258953491553/500000000000 : ℝ) (103581396623/200000000000 : ℝ) (410779459979/500000000000 : ℝ) (102694864997/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0426_exp_lower
  have heNumeric : (2019023258573/1000000000000 : ℝ)/4 ≤ Real.exp (-2734722008029/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023258573/1000000000000 : ℝ)/4 ≤ Real.exp ((2259/16384 : ℝ)-(102694864997/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2259/16384 : ℝ) (9037/65536 : ℝ) (102694864997/125000000000 : ℝ) (2019023258573/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0427; no trusted numerical premise.
theorem cover7_leaf0427_exp_radius : (19950807405900903/20000000000000000 : ℝ) ≤ Real.exp ((-4519/229376 : ℝ)/8) ∧ Real.exp ((-4519/229376 : ℝ)/8) ≤ (997540370295045151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4519/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0427_exp_lower : (459044911299129597/500000000000000000 : ℝ) ≤ Real.exp ((-10938886039123/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938886039123/16000000000000 : ℝ)/8) ≤ (183617964519651839/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938886039123/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0427_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023510067/1000000000000 : ℝ) ≤ 4*Real.exp (9037/65536 : ℝ)*Real.exp (-mu (radius 7 (4519/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023510067/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4519/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0427_exp_radius
  have hrNumeric : (980491525417/1000000000000 : ℝ) ≤ Real.exp (-4519/229376 : ℝ) ∧ Real.exp (-4519/229376 : ℝ) ≤ (490245762709/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980491525417/1000000000000 : ℝ) ≤ (radius 7 (4519/32768 : ℝ)) ∧ (radius 7 (4519/32768 : ℝ)) ≤ (490245762709/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4519/32768 : ℝ)) (980491525417/1000000000000 : ℝ) (490245762709/500000000000 : ℝ) (9828068043/50000000000 : ℝ) (98280680433/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4519/32768 : ℝ)) (980491525417/1000000000000 : ℝ) (490245762709/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980491525417/1000000000000 : ℝ) (490245762709/500000000000 : ℝ) (247561440677/250000000000 : ℝ) (990245762709/1000000000000 : ℝ) (198039544073/200000000000 : ℝ) (495098860183/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 1 (247561440677/250000000000 : ℝ) (990245762709/1000000000000 : ℝ) (198039544073/200000000000 : ℝ) (495098860183/500000000000 : ℝ) (30944429423/31250000000 : ℝ) (495110870769/500000000000 : ℝ) (198044348249/200000000000 : ℝ) (990221741247/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 2 (30944429423/31250000000 : ℝ) (495110870769/500000000000 : ℝ) (198044348249/200000000000 : ℝ) (990221741247/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 3 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 4 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 5 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 6 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4519/32768 : ℝ)) 7 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4519/32768 : ℝ))) (9828068043/50000000000 : ℝ) (98280680433/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9828068043/50000000000 : ℝ) (98280680433/500000000000 : ℝ) (59828068043/100000000000 : ℝ) (598280680433/1000000000000 : ℝ) (221676205793/500000000000 : ℝ) (221676205797/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 1 (59828068043/100000000000 : ℝ) (598280680433/1000000000000 : ℝ) (221676205793/500000000000 : ℝ) (221676205797/500000000000 : ℝ) (65102068251/125000000000 : ℝ) (260408273007/500000000000 : ℝ) (257511738797/500000000000 : ℝ) (515023477601/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 2 (65102068251/125000000000 : ℝ) (260408273007/500000000000 : ℝ) (257511738797/500000000000 : ℝ) (515023477601/1000000000000 : ℝ) (517920011801/1000000000000 : ℝ) (16185000369/31250000000 : ℝ) (517911912117/1000000000000 : ℝ) (4143295297/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 3 (517920011801/1000000000000 : ℝ) (16185000369/31250000000 : ℝ) (517911912117/1000000000000 : ℝ) (4143295297/8000000000 : ℝ) (517915961959/1000000000000 : ℝ) (517915961967/1000000000000 : ℝ) (517915961943/1000000000000 : ℝ) (517915961951/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 4 (517915961959/1000000000000 : ℝ) (517915961967/1000000000000 : ℝ) (517915961943/1000000000000 : ℝ) (517915961951/1000000000000 : ℝ) (517915961951/1000000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 5 (517915961951/1000000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 6 (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4519/32768 : ℝ))) 7 (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4519/32768 : ℝ)) hmem 8 (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4519/32768 : ℝ))) hcmem 8 (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4519/32768 : ℝ)) (99022174139/100000000000 : ℝ) (990221741393/1000000000000 : ℝ) (10358319239/20000000000 : ℝ) (517915961959/1000000000000 : ℝ) (410787027093/500000000000 : ℝ) (821574054203/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0427_exp_lower
  have heNumeric : (2019023510067/1000000000000 : ℝ)/4 ≤ Real.exp (-10938886039123/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023510067/1000000000000 : ℝ)/4 ≤ Real.exp ((9037/65536 : ℝ)-(821574054203/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9037/65536 : ℝ) (4519/32768 : ℝ) (821574054203/1000000000000 : ℝ) (2019023510067/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0428; no trusted numerical premise.
theorem cover7_leaf0428_exp_radius : (249385024621725493/250000000000000000 : ℝ) ≤ Real.exp ((-9039/458752 : ℝ)/8) ∧ Real.exp ((-9039/458752 : ℝ)/8) ≤ (997540098486901973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9039/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0428_exp_lower : (45904491851015499/50000000000000000 : ℝ) ≤ Real.exp ((-5469442014201/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469442014201/8000000000000 : ℝ)/8) ≤ (918089837020309981/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469442014201/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0428_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009511881899/500000000000 : ℝ) ≤ 4*Real.exp (4519/32768 : ℝ)*Real.exp (-mu (radius 7 (9039/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009511881899/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9039/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0428_exp_radius
  have hrNumeric : (980489388117/1000000000000 : ℝ) ≤ Real.exp (-9039/458752 : ℝ) ∧ Real.exp (-9039/458752 : ℝ) ≤ (490244694059/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980489388117/1000000000000 : ℝ) ≤ (radius 7 (9039/65536 : ℝ)) ∧ (radius 7 (9039/65536 : ℝ)) ≤ (490244694059/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9039/65536 : ℝ)) (980489388117/1000000000000 : ℝ) (490244694059/500000000000 : ℝ) (39314404377/200000000000 : ℝ) (196572021891/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9039/65536 : ℝ)) (980489388117/1000000000000 : ℝ) (490244694059/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980489388117/1000000000000 : ℝ) (490244694059/500000000000 : ℝ) (495122347029/500000000000 : ℝ) (990244694059/1000000000000 : ℝ) (198039328227/200000000000 : ℝ) (990196641137/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 1 (495122347029/500000000000 : ℝ) (990244694059/1000000000000 : ℝ) (198039328227/200000000000 : ℝ) (990196641137/1000000000000 : ℝ) (247555166899/250000000000 : ℝ) (495110333799/500000000000 : ℝ) (198044133461/200000000000 : ℝ) (990220667307/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 2 (247555166899/250000000000 : ℝ) (495110333799/500000000000 : ℝ) (198044133461/200000000000 : ℝ) (990220667307/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 3 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 4 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 5 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 6 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9039/65536 : ℝ)) 7 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9039/65536 : ℝ))) (39314404377/200000000000 : ℝ) (196572021891/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39314404377/200000000000 : ℝ) (196572021891/1000000000000 : ℝ) (299143005471/500000000000 : ℝ) (299143005473/500000000000 : ℝ) (221682217309/500000000000 : ℝ) (221682217313/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 1 (299143005471/500000000000 : ℝ) (299143005473/500000000000 : ℝ) (221682217309/500000000000 : ℝ) (221682217313/500000000000 : ℝ) (26041261139/50000000000 : ℝ) (260412611393/500000000000 : ℝ) (2060131021/4000000000 : ℝ) (257516377629/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 2 (26041261139/50000000000 : ℝ) (260412611393/500000000000 : ℝ) (2060131021/4000000000 : ℝ) (257516377629/500000000000 : ℝ) (103585797803/200000000000 : ℝ) (258964494511/500000000000 : ℝ) (32370055697/62500000000 : ℝ) (12948022279/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 3 (103585797803/200000000000 : ℝ) (258964494511/500000000000 : ℝ) (32370055697/62500000000 : ℝ) (12948022279/25000000000 : ℝ) (517924940083/1000000000000 : ℝ) (517924940091/1000000000000 : ℝ) (517924940067/1000000000000 : ℝ) (129481235019/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 4 (517924940083/1000000000000 : ℝ) (517924940091/1000000000000 : ℝ) (517924940067/1000000000000 : ℝ) (129481235019/250000000000 : ℝ) (20716997603/40000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 5 (20716997603/40000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 6 (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9039/65536 : ℝ))) 7 (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9039/65536 : ℝ)) hmem 8 (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9039/65536 : ℝ))) hcmem 8 (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9039/65536 : ℝ)) (19804413349/20000000000 : ℝ) (990220667453/1000000000000 : ℝ) (258962470037/500000000000 : ℝ) (129481235021/250000000000 : ℝ) (821589187303/1000000000000 : ℝ) (410794593661/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0428_exp_lower
  have heNumeric : (1009511881899/500000000000 : ℝ)/4 ≤ Real.exp (-5469442014201/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009511881899/500000000000 : ℝ)/4 ≤ Real.exp ((4519/32768 : ℝ)-(410794593661/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4519/32768 : ℝ) (9039/65536 : ℝ) (410794593661/500000000000 : ℝ) (1009511881899/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0429; no trusted numerical premise.
theorem cover7_leaf0429_exp_radius : (997539826678832857/1000000000000000000 : ℝ) ≤ Real.exp ((-565/28672 : ℝ)/8) ∧ Real.exp ((-565/28672 : ℝ)/8) ≤ (498769913339416429/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-565/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0429_exp_lower : (459044925785676309/500000000000000000 : ℝ) ≤ Real.exp ((-10938881999697/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938881999697/16000000000000 : ℝ)/8) ≤ (918089851571352619/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938881999697/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0429_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512009899/500000000000 : ℝ) ≤ 4*Real.exp (9039/65536 : ℝ)*Real.exp (-mu (radius 7 (565/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512009899/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (565/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0429_exp_radius
  have hrNumeric : (490243625411/500000000000 : ℝ) ≤ Real.exp (-565/28672 : ℝ) ∧ Real.exp (-565/28672 : ℝ) ≤ (980487250823/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490243625411/500000000000 : ℝ) ≤ (radius 7 (565/4096 : ℝ)) ∧ (radius 7 (565/4096 : ℝ)) ≤ (980487250823/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (565/4096 : ℝ)) (490243625411/500000000000 : ℝ) (980487250823/1000000000000 : ℝ) (98291341141/500000000000 : ℝ) (12286417643/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (565/4096 : ℝ)) (490243625411/500000000000 : ℝ) (980487250823/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (565/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490243625411/500000000000 : ℝ) (980487250823/1000000000000 : ℝ) (990243625411/1000000000000 : ℝ) (247560906353/250000000000 : ℝ) (990195561907/1000000000000 : ℝ) (990195561909/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (565/4096 : ℝ)) 1 (990243625411/1000000000000 : ℝ) (247560906353/250000000000 : ℝ) (990195561907/1000000000000 : ℝ) (990195561909/1000000000000 : ℝ) (990219593659/1000000000000 : ℝ) (990219593661/1000000000000 : ℝ) (990219593367/1000000000000 : ℝ) (990219593369/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (565/4096 : ℝ)) 2 (990219593659/1000000000000 : ℝ) (990219593661/1000000000000 : ℝ) (990219593367/1000000000000 : ℝ) (990219593369/1000000000000 : ℝ) (990219593513/1000000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (565/4096 : ℝ)) 3 (990219593513/1000000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (565/4096 : ℝ)) 4 (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (565/4096 : ℝ)) 5 (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (565/4096 : ℝ)) 6 (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (565/4096 : ℝ)) 7 (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (565/4096 : ℝ))) (98291341141/500000000000 : ℝ) (12286417643/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98291341141/500000000000 : ℝ) (12286417643/62500000000 : ℝ) (598291341141/1000000000000 : ℝ) (74786417643/125000000000 : ℝ) (55422057077/125000000000 : ℝ) (27711028539/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 1 (598291341141/1000000000000 : ℝ) (74786417643/125000000000 : ℝ) (55422057077/125000000000 : ℝ) (27711028539/62500000000 : ℝ) (260416949439/500000000000 : ℝ) (130208474721/250000000000 : ℝ) (1005941469/1953125000 : ℝ) (103008406427/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 2 (260416949439/500000000000 : ℝ) (130208474721/250000000000 : ℝ) (1005941469/1953125000 : ℝ) (103008406427/200000000000 : ℝ) (517937965503/1000000000000 : ℝ) (51793796551/100000000000 : ℝ) (25896493473/50000000000 : ℝ) (517929869467/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 3 (517937965503/1000000000000 : ℝ) (51793796551/100000000000 : ℝ) (25896493473/50000000000 : ℝ) (517929869467/1000000000000 : ℝ) (517933917481/1000000000000 : ℝ) (517933917489/1000000000000 : ℝ) (103586783493/200000000000 : ℝ) (517933917473/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 4 (517933917481/1000000000000 : ℝ) (517933917489/1000000000000 : ℝ) (103586783493/200000000000 : ℝ) (517933917473/1000000000000 : ℝ) (517933917473/1000000000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 5 (517933917473/1000000000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 6 (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (565/4096 : ℝ))) 7 (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (565/4096 : ℝ)) hmem 8 (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (565/4096 : ℝ))) hcmem 8 (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (565/4096 : ℝ)) (123777449189/125000000000 : ℝ) (198043918703/200000000000 : ℝ) (16185434921/31250000000 : ℝ) (517933917481/1000000000000 : ℝ) (8216043193/10000000000 : ℝ) (821604319317/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0429_exp_lower
  have heNumeric : (1009512009899/500000000000 : ℝ)/4 ≤ Real.exp (-10938881999697/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512009899/500000000000 : ℝ)/4 ≤ Real.exp ((9039/65536 : ℝ)-(821604319317/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9039/65536 : ℝ) (565/4096 : ℝ) (821604319317/1000000000000 : ℝ) (1009512009899/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0430; no trusted numerical premise.
theorem cover7_leaf0430_exp_radius : (997539554870837803/1000000000000000000 : ℝ) ≤ Real.exp ((-9041/458752 : ℝ)/8) ∧ Real.exp ((-9041/458752 : ℝ)/8) ≤ (249384888717709451/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9041/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0430_exp_lower : (918089866250354261/1000000000000000000 : ℝ) ≤ Real.exp ((-42729999817/62500000000 : ℝ)/8) ∧ Real.exp ((-42729999817/62500000000 : ℝ)/8) ≤ (459044933125177131/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42729999817/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0430_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024278049/1000000000000 : ℝ) ≤ 4*Real.exp (565/4096 : ℝ)*Real.exp (-mu (radius 7 (9041/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024278049/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9041/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0430_exp_radius
  have hrNumeric : (245121278383/250000000000 : ℝ) ≤ Real.exp (-9041/458752 : ℝ) ∧ Real.exp (-9041/458752 : ℝ) ≤ (980485113533/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245121278383/250000000000 : ℝ) ≤ (radius 7 (9041/65536 : ℝ)) ∧ (radius 7 (9041/65536 : ℝ)) ≤ (980485113533/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9041/65536 : ℝ)) (245121278383/250000000000 : ℝ) (980485113533/1000000000000 : ℝ) (98296671027/500000000000 : ℝ) (9829667103/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9041/65536 : ℝ)) (245121278383/250000000000 : ℝ) (980485113533/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245121278383/250000000000 : ℝ) (980485113533/1000000000000 : ℝ) (495121278383/500000000000 : ℝ) (990242556767/1000000000000 : ℝ) (990194482681/1000000000000 : ℝ) (495097241341/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 1 (495121278383/500000000000 : ℝ) (990242556767/1000000000000 : ℝ) (990194482681/1000000000000 : ℝ) (495097241341/500000000000 : ℝ) (990218519723/1000000000000 : ℝ) (39608740789/40000000000 : ℝ) (990218519431/1000000000000 : ℝ) (990218519433/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 2 (990218519723/1000000000000 : ℝ) (39608740789/40000000000 : ℝ) (990218519431/1000000000000 : ℝ) (990218519433/1000000000000 : ℝ) (990218519577/1000000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 3 (990218519577/1000000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 4 (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 5 (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 6 (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9041/65536 : ℝ)) 7 (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9041/65536 : ℝ))) (98296671027/500000000000 : ℝ) (9829667103/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98296671027/500000000000 : ℝ) (9829667103/50000000000 : ℝ) (598296671027/1000000000000 : ℝ) (59829667103/100000000000 : ℝ) (443388477583/1000000000000 : ℝ) (443388477591/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 1 (598296671027/1000000000000 : ℝ) (59829667103/100000000000 : ℝ) (443388477583/1000000000000 : ℝ) (443388477591/1000000000000 : ℝ) (104168514861/200000000000 : ℝ) (520842574311/1000000000000 : ℝ) (51505130823/100000000000 : ℝ) (515051308237/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 2 (104168514861/200000000000 : ℝ) (520842574311/1000000000000 : ℝ) (51505130823/100000000000 : ℝ) (515051308237/1000000000000 : ℝ) (517946941267/1000000000000 : ℝ) (258973470637/500000000000 : ℝ) (129484711761/250000000000 : ℝ) (517938847051/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 3 (517946941267/1000000000000 : ℝ) (258973470637/500000000000 : ℝ) (129484711761/250000000000 : ℝ) (517938847051/1000000000000 : ℝ) (103588578831/200000000000 : ℝ) (517942894163/1000000000000 : ℝ) (517942894139/1000000000000 : ℝ) (517942894147/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 4 (103588578831/200000000000 : ℝ) (517942894163/1000000000000 : ℝ) (517942894139/1000000000000 : ℝ) (517942894147/1000000000000 : ℝ) (517942894147/1000000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 5 (517942894147/1000000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 6 (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9041/65536 : ℝ))) 7 (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9041/65536 : ℝ)) hmem 8 (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9041/65536 : ℝ))) hcmem 8 (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9041/65536 : ℝ)) (123777314947/125000000000 : ℝ) (990218519579/1000000000000 : ℝ) (258971447073/500000000000 : ℝ) (103588578831/200000000000 : ℝ) (821619450179/1000000000000 : ℝ) (821619450197/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0430_exp_lower
  have heNumeric : (2019024278049/1000000000000 : ℝ)/4 ≤ Real.exp (-42729999817/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024278049/1000000000000 : ℝ)/4 ≤ Real.exp ((565/4096 : ℝ)-(821619450197/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (565/4096 : ℝ) (9041/65536 : ℝ) (821619450197/1000000000000 : ℝ) (2019024278049/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0431; no trusted numerical premise.
theorem cover7_leaf0431_exp_radius : (997539283062916811/1000000000000000000 : ℝ) ≤ Real.exp ((-4521/229376 : ℝ)/8) ∧ Real.exp ((-4521/229376 : ℝ)/8) ≤ (249384820765729203/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4521/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0431_exp_lower : (114761235132121329/125000000000000000 : ℝ) ≤ Real.exp ((-2187775577763/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187775577763/3200000000000 : ℝ)/8) ≤ (918089881056970633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187775577763/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0431_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512269273/500000000000 : ℝ) ≤ 4*Real.exp (9041/65536 : ℝ)*Real.exp (-mu (radius 7 (4521/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512269273/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4521/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0431_exp_radius
  have hrNumeric : (490241488123/500000000000 : ℝ) ≤ Real.exp (-4521/229376 : ℝ) ∧ Real.exp (-4521/229376 : ℝ) ≤ (980482976247/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490241488123/500000000000 : ℝ) ≤ (radius 7 (4521/32768 : ℝ)) ∧ (radius 7 (4521/32768 : ℝ)) ≤ (980482976247/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4521/32768 : ℝ)) (490241488123/500000000000 : ℝ) (980482976247/1000000000000 : ℝ) (39320800241/200000000000 : ℝ) (196604001211/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4521/32768 : ℝ)) (490241488123/500000000000 : ℝ) (980482976247/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490241488123/500000000000 : ℝ) (980482976247/1000000000000 : ℝ) (990241488123/1000000000000 : ℝ) (247560372031/250000000000 : ℝ) (198038680691/200000000000 : ℝ) (15471771929/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 1 (990241488123/1000000000000 : ℝ) (247560372031/250000000000 : ℝ) (198038680691/200000000000 : ℝ) (15471771929/15625000000 : ℝ) (990217445789/1000000000000 : ℝ) (99021744579/100000000000 : ℝ) (990217445497/1000000000000 : ℝ) (990217445499/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 2 (990217445789/1000000000000 : ℝ) (99021744579/100000000000 : ℝ) (990217445497/1000000000000 : ℝ) (990217445499/1000000000000 : ℝ) (990217445643/1000000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 3 (990217445643/1000000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 4 (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 5 (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 6 (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4521/32768 : ℝ)) 7 (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4521/32768 : ℝ))) (39320800241/200000000000 : ℝ) (196604001211/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39320800241/200000000000 : ℝ) (196604001211/1000000000000 : ℝ) (299151000301/500000000000 : ℝ) (299151000303/500000000000 : ℝ) (110850124381/250000000000 : ℝ) (110850124383/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 1 (299151000301/500000000000 : ℝ) (299151000303/500000000000 : ℝ) (110850124381/250000000000 : ℝ) (110850124383/250000000000 : ℝ) (520851249063/1000000000000 : ℝ) (520851249069/1000000000000 : ℝ) (515060583559/1000000000000 : ℝ) (257530291783/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 2 (520851249063/1000000000000 : ℝ) (520851249069/1000000000000 : ℝ) (515060583559/1000000000000 : ℝ) (257530291783/500000000000 : ℝ) (517955916311/1000000000000 : ℝ) (258977958159/500000000000 : ℝ) (258973911953/500000000000 : ℝ) (258973911957/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 3 (517955916311/1000000000000 : ℝ) (258977958159/500000000000 : ℝ) (258973911953/500000000000 : ℝ) (258973911957/500000000000 : ℝ) (129487967527/250000000000 : ℝ) (129487967529/250000000000 : ℝ) (129487967523/250000000000 : ℝ) (517951870101/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 4 (129487967527/250000000000 : ℝ) (129487967529/250000000000 : ℝ) (129487967523/250000000000 : ℝ) (517951870101/1000000000000 : ℝ) (5179518701/10000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 5 (5179518701/10000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 6 (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4521/32768 : ℝ))) 7 (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4521/32768 : ℝ)) hmem 8 (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4521/32768 : ℝ))) hcmem 8 (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4521/32768 : ℝ)) (495108722821/500000000000 : ℝ) (198043489129/200000000000 : ℝ) (517951870099/1000000000000 : ℝ) (517951870109/1000000000000 : ℝ) (410817289973/500000000000 : ℝ) (164326915993/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0431_exp_lower
  have heNumeric : (1009512269273/500000000000 : ℝ)/4 ≤ Real.exp (-2187775577763/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512269273/500000000000 : ℝ)/4 ≤ Real.exp ((9041/65536 : ℝ)-(164326915993/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9041/65536 : ℝ) (4521/32768 : ℝ) (164326915993/200000000000 : ℝ) (1009512269273/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0432; no trusted numerical premise.
theorem cover7_leaf0432_exp_radius : (997539011255069881/1000000000000000000 : ℝ) ≤ Real.exp ((-9043/458752 : ℝ)/8) ∧ Real.exp ((-9043/458752 : ℝ)/8) ≤ (498769505627534941/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9043/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0432_exp_lower : (229522473998058647/250000000000000000 : ℝ) ≤ Real.exp ((-5469437903271/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469437903271/8000000000000 : ℝ)/8) ≤ (918089895992234589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469437903271/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0432_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512400653/500000000000 : ℝ) ≤ 4*Real.exp (4521/32768 : ℝ)*Real.exp (-mu (radius 7 (9043/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512400653/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9043/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0432_exp_radius
  have hrNumeric : (196096167793/200000000000 : ℝ) ≤ Real.exp (-9043/458752 : ℝ) ∧ Real.exp (-9043/458752 : ℝ) ≤ (490240419483/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196096167793/200000000000 : ℝ) ≤ (radius 7 (9043/65536 : ℝ)) ∧ (radius 7 (9043/65536 : ℝ)) ≤ (490240419483/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9043/65536 : ℝ)) (196096167793/200000000000 : ℝ) (490240419483/500000000000 : ℝ) (196614659729/1000000000000 : ℝ) (39322931947/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9043/65536 : ℝ)) (196096167793/200000000000 : ℝ) (490240419483/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196096167793/200000000000 : ℝ) (490240419483/500000000000 : ℝ) (495120209741/500000000000 : ℝ) (990240419483/1000000000000 : ℝ) (99019232423/100000000000 : ℝ) (123774040529/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 1 (495120209741/500000000000 : ℝ) (990240419483/1000000000000 : ℝ) (99019232423/100000000000 : ℝ) (123774040529/125000000000 : ℝ) (61888523241/62500000000 : ℝ) (495108185929/500000000000 : ℝ) (990216371563/1000000000000 : ℝ) (495108185783/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 2 (61888523241/62500000000 : ℝ) (495108185929/500000000000 : ℝ) (990216371563/1000000000000 : ℝ) (495108185783/500000000000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 3 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 4 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 5 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 6 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9043/65536 : ℝ)) 7 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9043/65536 : ℝ))) (196614659729/1000000000000 : ℝ) (39322931947/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196614659729/1000000000000 : ℝ) (39322931947/200000000000 : ℝ) (74788416233/125000000000 : ℝ) (149576832467/250000000000 : ℝ) (27713282277/62500000000 : ℝ) (11085312911/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 1 (74788416233/125000000000 : ℝ) (149576832467/250000000000 : ℝ) (27713282277/62500000000 : ℝ) (11085312911/25000000000 : ℝ) (130214980787/250000000000 : ℝ) (260429961577/500000000000 : ℝ) (515069858111/1000000000000 : ℝ) (257534929059/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 2 (130214980787/250000000000 : ℝ) (260429961577/500000000000 : ℝ) (515069858111/1000000000000 : ℝ) (257534929059/500000000000 : ℝ) (517964890629/1000000000000 : ℝ) (129491222659/250000000000 : ℝ) (517956800043/1000000000000 : ℝ) (517956800051/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 3 (517964890629/1000000000000 : ℝ) (129491222659/250000000000 : ℝ) (517956800043/1000000000000 : ℝ) (517956800051/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (16186276417/31250000000 : ℝ) (12949021133/25000000000 : ℝ) (32372552833/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 4 (64745105667/125000000000 : ℝ) (16186276417/31250000000 : ℝ) (12949021133/25000000000 : ℝ) (32372552833/62500000000 : ℝ) (32372552833/62500000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 5 (32372552833/62500000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 6 (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9043/65536 : ℝ))) 7 (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9043/65536 : ℝ)) hmem 8 (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9043/65536 : ℝ))) hcmem 8 (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9043/65536 : ℝ)) (990216371709/1000000000000 : ℝ) (1934016351/1953125000 : ℝ) (517960845327/1000000000000 : ℝ) (64745105667/125000000000 : ℝ) (164329941719/200000000000 : ℝ) (205412427153/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0432_exp_lower
  have heNumeric : (1009512400653/500000000000 : ℝ)/4 ≤ Real.exp (-5469437903271/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512400653/500000000000 : ℝ)/4 ≤ Real.exp ((4521/32768 : ℝ)-(205412427153/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4521/32768 : ℝ) (9043/65536 : ℝ) (205412427153/250000000000 : ℝ) (1009512400653/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0433; no trusted numerical premise.
theorem cover7_leaf0433_exp_radius : (997538739447297013/1000000000000000000 : ℝ) ≤ Real.exp ((-323/16384 : ℝ)/8) ∧ Real.exp ((-323/16384 : ℝ)/8) ≤ (498769369723648507/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-323/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0433_exp_lower : (229522477763921773/250000000000000000 : ℝ) ≤ Real.exp ((-10938873706397/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938873706397/16000000000000 : ℝ)/8) ≤ (918089911055687093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938873706397/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0433_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512533161/500000000000 : ℝ) ≤ 4*Real.exp (9043/65536 : ℝ)*Real.exp (-mu (radius 7 (2261/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512533161/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2261/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0433_exp_radius
  have hrNumeric : (980478701689/1000000000000 : ℝ) ≤ Real.exp (-323/16384 : ℝ) ∧ Real.exp (-323/16384 : ℝ) ≤ (98047870169/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980478701689/1000000000000 : ℝ) ≤ (radius 7 (2261/16384 : ℝ)) ∧ (radius 7 (2261/16384 : ℝ)) ≤ (98047870169/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2261/16384 : ℝ)) (980478701689/1000000000000 : ℝ) (98047870169/100000000000 : ℝ) (196625317627/1000000000000 : ℝ) (196625317633/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2261/16384 : ℝ)) (980478701689/1000000000000 : ℝ) (98047870169/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980478701689/1000000000000 : ℝ) (98047870169/100000000000 : ℝ) (247559837711/250000000000 : ℝ) (198047870169/200000000000 : ℝ) (990191245007/1000000000000 : ℝ) (61886952813/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 1 (247559837711/250000000000 : ℝ) (198047870169/200000000000 : ℝ) (990191245007/1000000000000 : ℝ) (61886952813/62500000000 : ℝ) (39608611917/40000000000 : ℝ) (990215297927/1000000000000 : ℝ) (990215297633/1000000000000 : ℝ) (198043059527/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 2 (39608611917/40000000000 : ℝ) (990215297927/1000000000000 : ℝ) (990215297633/1000000000000 : ℝ) (198043059527/200000000000 : ℝ) (990215297779/1000000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 3 (990215297779/1000000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 4 (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 5 (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 6 (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2261/16384 : ℝ)) 7 (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2261/16384 : ℝ))) (196625317627/1000000000000 : ℝ) (196625317633/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196625317627/1000000000000 : ℝ) (196625317633/1000000000000 : ℝ) (598312658813/1000000000000 : ℝ) (598312658817/1000000000000 : ℝ) (110856133577/250000000000 : ℝ) (110856133579/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 1 (598312658813/1000000000000 : ℝ) (598312658817/1000000000000 : ℝ) (110856133577/250000000000 : ℝ) (110856133579/250000000000 : ℝ) (6510857457/12500000000 : ℝ) (520868596567/1000000000000 : ℝ) (257539565943/500000000000 : ℝ) (515079131893/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 2 (6510857457/12500000000 : ℝ) (520868596567/1000000000000 : ℝ) (257539565943/500000000000 : ℝ) (515079131893/1000000000000 : ℝ) (517973864223/1000000000000 : ℝ) (51797386423/100000000000 : ℝ) (103593155091/200000000000 : ℝ) (517965775463/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 3 (517973864223/1000000000000 : ℝ) (51797386423/100000000000 : ℝ) (103593155091/200000000000 : ℝ) (517965775463/1000000000000 : ℝ) (517969819839/1000000000000 : ℝ) (517969819847/1000000000000 : ℝ) (517969819823/1000000000000 : ℝ) (517969819831/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 4 (517969819839/1000000000000 : ℝ) (517969819847/1000000000000 : ℝ) (517969819823/1000000000000 : ℝ) (517969819831/1000000000000 : ℝ) (517969819831/1000000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 5 (517969819831/1000000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 6 (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2261/16384 : ℝ))) 7 (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2261/16384 : ℝ)) hmem 8 (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2261/16384 : ℝ))) hcmem 8 (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2261/16384 : ℝ)) (495107648889/500000000000 : ℝ) (990215297781/1000000000000 : ℝ) (51796981983/100000000000 : ℝ) (517969819839/1000000000000 : ℝ) (205416209031/250000000000 : ℝ) (410832418071/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0433_exp_lower
  have heNumeric : (1009512533161/500000000000 : ℝ)/4 ≤ Real.exp (-10938873706397/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512533161/500000000000 : ℝ)/4 ≤ Real.exp ((9043/65536 : ℝ)-(410832418071/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9043/65536 : ℝ) (2261/16384 : ℝ) (410832418071/500000000000 : ℝ) (1009512533161/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0434; no trusted numerical premise.
theorem cover7_leaf0434_exp_radius : (498769233819799103/500000000000000000 : ℝ) ≤ Real.exp ((-9045/458752 : ℝ)/8) ∧ Real.exp ((-9045/458752 : ℝ)/8) ≤ (997538467639598207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9045/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0434_exp_lower : (918089926247442909/1000000000000000000 : ℝ) ≤ Real.exp ((-2734717897091/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734717897091/4000000000000 : ℝ)/8) ≤ (91808992624744291/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734717897091/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0434_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512666797/500000000000 : ℝ) ≤ 4*Real.exp (2261/16384 : ℝ)*Real.exp (-mu (radius 7 (9045/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512666797/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9045/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0434_exp_radius
  have hrNumeric : (490238282209/500000000000 : ℝ) ≤ Real.exp (-9045/458752 : ℝ) ∧ Real.exp (-9045/458752 : ℝ) ≤ (980476564419/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490238282209/500000000000 : ℝ) ≤ (radius 7 (9045/65536 : ℝ)) ∧ (radius 7 (9045/65536 : ℝ)) ≤ (980476564419/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9045/65536 : ℝ)) (490238282209/500000000000 : ℝ) (980476564419/1000000000000 : ℝ) (1966359749/10000000000 : ℝ) (98317987453/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9045/65536 : ℝ)) (490238282209/500000000000 : ℝ) (980476564419/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490238282209/500000000000 : ℝ) (980476564419/1000000000000 : ℝ) (990238282209/1000000000000 : ℝ) (99023828221/100000000000 : ℝ) (198038033157/200000000000 : ℝ) (495095082893/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 1 (990238282209/1000000000000 : ℝ) (99023828221/100000000000 : ℝ) (198038033157/200000000000 : ℝ) (495095082893/500000000000 : ℝ) (990214223997/1000000000000 : ℝ) (495107111999/500000000000 : ℝ) (123776777963/125000000000 : ℝ) (495107111853/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 2 (990214223997/1000000000000 : ℝ) (495107111999/500000000000 : ℝ) (123776777963/125000000000 : ℝ) (495107111853/500000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 3 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 4 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 5 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 6 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9045/65536 : ℝ)) 7 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9045/65536 : ℝ))) (1966359749/10000000000 : ℝ) (98317987453/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1966359749/10000000000 : ℝ) (98317987453/500000000000 : ℝ) (11966359749/20000000000 : ℝ) (598317987453/1000000000000 : ℝ) (221718275577/500000000000 : ℝ) (221718275581/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 1 (11966359749/20000000000 : ℝ) (598317987453/1000000000000 : ℝ) (221718275577/500000000000 : ℝ) (221718275581/500000000000 : ℝ) (260438634651/500000000000 : ℝ) (130219317327/250000000000 : ℝ) (257544202443/500000000000 : ℝ) (515088404893/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 2 (260438634651/500000000000 : ℝ) (130219317327/250000000000 : ℝ) (257544202443/500000000000 : ℝ) (515088404893/1000000000000 : ℝ) (258991418547/500000000000 : ℝ) (517982837101/1000000000000 : ℝ) (517974750143/1000000000000 : ℝ) (10359495003/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 3 (258991418547/500000000000 : ℝ) (517982837101/1000000000000 : ℝ) (517974750143/1000000000000 : ℝ) (10359495003/20000000000 : ℝ) (258989396809/500000000000 : ℝ) (258989396813/500000000000 : ℝ) (258989396801/500000000000 : ℝ) (51797879361/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 4 (258989396809/500000000000 : ℝ) (258989396813/500000000000 : ℝ) (258989396801/500000000000 : ℝ) (51797879361/100000000000 : ℝ) (51797879361/100000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 5 (51797879361/100000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 6 (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9045/65536 : ℝ))) 7 (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9045/65536 : ℝ)) hmem 8 (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9045/65536 : ℝ))) hcmem 8 (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9045/65536 : ℝ)) (19804284477/20000000000 : ℝ) (247553555963/250000000000 : ℝ) (517978793609/1000000000000 : ℝ) (258989396809/500000000000 : ℝ) (821679962537/1000000000000 : ℝ) (410839981277/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0434_exp_lower
  have heNumeric : (1009512666797/500000000000 : ℝ)/4 ≤ Real.exp (-2734717897091/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512666797/500000000000 : ℝ)/4 ≤ Real.exp ((2261/16384 : ℝ)-(410839981277/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2261/16384 : ℝ) (9045/65536 : ℝ) (410839981277/500000000000 : ℝ) (1009512666797/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0435; no trusted numerical premise.
theorem cover7_leaf0435_exp_radius : (997538195831973461/1000000000000000000 : ℝ) ≤ Real.exp ((-4523/229376 : ℝ)/8) ∧ Real.exp ((-4523/229376 : ℝ)/8) ≤ (498769097915986731/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4523/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0435_exp_lower : (459044970783291979/500000000000000000 : ℝ) ≤ Real.exp ((-10938869452571/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938869452571/16000000000000 : ℝ)/8) ≤ (918089941566583959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938869452571/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0435_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504756400777/250000000000 : ℝ) ≤ 4*Real.exp (9045/65536 : ℝ)*Real.exp (-mu (radius 7 (4523/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504756400777/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4523/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0435_exp_radius
  have hrNumeric : (980474427151/1000000000000 : ℝ) ≤ Real.exp (-4523/229376 : ℝ) ∧ Real.exp (-4523/229376 : ℝ) ≤ (61279651697/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980474427151/1000000000000 : ℝ) ≤ (radius 7 (4523/32768 : ℝ)) ∧ (radius 7 (4523/32768 : ℝ)) ≤ (61279651697/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4523/32768 : ℝ)) (980474427151/1000000000000 : ℝ) (61279651697/62500000000 : ℝ) (1536301809/7812500000 : ℝ) (98323315779/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4523/32768 : ℝ)) (980474427151/1000000000000 : ℝ) (61279651697/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980474427151/1000000000000 : ℝ) (61279651697/62500000000 : ℝ) (39609488543/40000000000 : ℝ) (123779651697/125000000000 : ℝ) (247547271641/250000000000 : ℝ) (198037817313/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 1 (39609488543/40000000000 : ℝ) (123779651697/125000000000 : ℝ) (247547271641/250000000000 : ℝ) (198037817313/200000000000 : ℝ) (990213150069/1000000000000 : ℝ) (990213150071/1000000000000 : ℝ) (990213149777/1000000000000 : ℝ) (990213149779/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 2 (990213150069/1000000000000 : ℝ) (990213150071/1000000000000 : ℝ) (990213149777/1000000000000 : ℝ) (990213149779/1000000000000 : ℝ) (990213149923/1000000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 3 (990213149923/1000000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 4 (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 5 (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 6 (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4523/32768 : ℝ)) 7 (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4523/32768 : ℝ))) (1536301809/7812500000 : ℝ) (98323315779/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1536301809/7812500000 : ℝ) (98323315779/500000000000 : ℝ) (9348801809/15625000000 : ℝ) (598323315779/1000000000000 : ℝ) (221724283487/500000000000 : ℝ) (221724283491/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 1 (9348801809/15625000000 : ℝ) (598323315779/1000000000000 : ℝ) (221724283487/500000000000 : ℝ) (221724283491/500000000000 : ℝ) (4167087531/8000000000 : ℝ) (520885941381/1000000000000 : ℝ) (515097677113/1000000000000 : ℝ) (1609680241/3125000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 2 (4167087531/8000000000 : ℝ) (520885941381/1000000000000 : ℝ) (515097677113/1000000000000 : ℝ) (1609680241/3125000000 : ℝ) (129497952311/250000000000 : ℝ) (517991809251/1000000000000 : ℝ) (51798372411/100000000000 : ℝ) (517983724117/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 3 (129497952311/250000000000 : ℝ) (517991809251/1000000000000 : ℝ) (51798372411/100000000000 : ℝ) (517983724117/1000000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941671/250000000000 : ℝ) (517987766661/1000000000000 : ℝ) (517987766669/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 4 (517987766677/1000000000000 : ℝ) (129496941671/250000000000 : ℝ) (517987766661/1000000000000 : ℝ) (517987766669/1000000000000 : ℝ) (517987766669/1000000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 5 (517987766669/1000000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 6 (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4523/32768 : ℝ))) 7 (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4523/32768 : ℝ)) hmem 8 (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4523/32768 : ℝ))) hcmem 8 (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4523/32768 : ℝ)) (495106574961/500000000000 : ℝ) (39608525997/40000000000 : ℝ) (129496941667/250000000000 : ℝ) (517987766677/1000000000000 : ℝ) (410847543919/500000000000 : ℝ) (51355942991/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0435_exp_lower
  have heNumeric : (504756400777/250000000000 : ℝ)/4 ≤ Real.exp (-10938869452571/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504756400777/250000000000 : ℝ)/4 ≤ Real.exp ((9045/65536 : ℝ)-(51355942991/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9045/65536 : ℝ) (4523/32768 : ℝ) (51355942991/62500000000 : ℝ) (504756400777/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0436; no trusted numerical premise.
theorem cover7_leaf0436_exp_radius : (498768962012211389/500000000000000000 : ℝ) ≤ Real.exp ((-9047/458752 : ℝ)/8) ∧ Real.exp ((-9047/458752 : ℝ)/8) ≤ (997537924024422779/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9047/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0436_exp_lower : (918089957013454527/1000000000000000000 : ℝ) ≤ Real.exp ((-1093886729897/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093886729897/1600000000000 : ℝ)/8) ≤ (14345155578335227/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093886729897/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0436_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019025874869/1000000000000 : ℝ) ≤ 4*Real.exp (4523/32768 : ℝ)*Real.exp (-mu (radius 7 (9047/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019025874869/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9047/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0436_exp_radius
  have hrNumeric : (30639759059/31250000000 : ℝ) ≤ Real.exp (-9047/458752 : ℝ) ∧ Real.exp (-9047/458752 : ℝ) ≤ (980472289889/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30639759059/31250000000 : ℝ) ≤ (radius 7 (9047/65536 : ℝ)) ∧ (radius 7 (9047/65536 : ℝ)) ≤ (980472289889/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9047/65536 : ℝ)) (30639759059/31250000000 : ℝ) (980472289889/1000000000000 : ℝ) (196657287583/1000000000000 : ℝ) (196657287589/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9047/65536 : ℝ)) (30639759059/31250000000 : ℝ) (980472289889/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30639759059/31250000000 : ℝ) (980472289889/1000000000000 : ℝ) (61889759059/62500000000 : ℝ) (198047228989/200000000000 : ℝ) (61886750459/62500000000 : ℝ) (198037601469/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 1 (61889759059/62500000000 : ℝ) (198047228989/200000000000 : ℝ) (61886750459/62500000000 : ℝ) (198037601469/200000000000 : ℝ) (61888254759/62500000000 : ℝ) (198042415229/200000000000 : ℝ) (990212075851/1000000000000 : ℝ) (990212075853/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 2 (61888254759/62500000000 : ℝ) (198042415229/200000000000 : ℝ) (990212075851/1000000000000 : ℝ) (990212075853/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 3 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 4 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 5 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 6 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9047/65536 : ℝ)) 7 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9047/65536 : ℝ))) (196657287583/1000000000000 : ℝ) (196657287589/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196657287583/1000000000000 : ℝ) (196657287589/1000000000000 : ℝ) (598328643791/1000000000000 : ℝ) (119665728759/200000000000 : ℝ) (443460581769/1000000000000 : ℝ) (27716286361/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 1 (598328643791/1000000000000 : ℝ) (119665728759/200000000000 : ℝ) (443460581769/1000000000000 : ℝ) (27716286361/62500000000 : ℝ) (26044730639/50000000000 : ℝ) (260447306393/500000000000 : ℝ) (515106948569/1000000000000 : ℝ) (16097092143/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 2 (26044730639/50000000000 : ℝ) (260447306393/500000000000 : ℝ) (515106948569/1000000000000 : ℝ) (16097092143/31250000000 : ℝ) (259000390337/500000000000 : ℝ) (518000780681/1000000000000 : ℝ) (129498174339/250000000000 : ℝ) (129498174341/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 3 (259000390337/500000000000 : ℝ) (518000780681/1000000000000 : ℝ) (129498174339/250000000000 : ℝ) (129498174341/250000000000 : ℝ) (103599347803/200000000000 : ℝ) (517996739023/1000000000000 : ℝ) (517996738999/1000000000000 : ℝ) (517996739007/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 4 (103599347803/200000000000 : ℝ) (517996739023/1000000000000 : ℝ) (517996738999/1000000000000 : ℝ) (517996739007/1000000000000 : ℝ) (517996739007/1000000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 5 (517996739007/1000000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 6 (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9047/65536 : ℝ))) 7 (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9047/65536 : ℝ)) hmem 8 (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9047/65536 : ℝ))) hcmem 8 (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9047/65536 : ℝ)) (990212075997/1000000000000 : ℝ) (990212075999/1000000000000 : ℝ) (258998369503/500000000000 : ℝ) (103599347803/200000000000 : ℝ) (205427553007/250000000000 : ℝ) (164342042409/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0436_exp_lower
  have heNumeric : (2019025874869/1000000000000 : ℝ)/4 ≤ Real.exp (-1093886729897/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019025874869/1000000000000 : ℝ)/4 ≤ Real.exp ((4523/32768 : ℝ)-(164342042409/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4523/32768 : ℝ) (9047/65536 : ℝ) (164342042409/200000000000 : ℝ) (2019025874869/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0437; no trusted numerical premise.
theorem cover7_leaf0437_exp_radius : (997537652216946157/1000000000000000000 : ℝ) ≤ Real.exp ((-1131/57344 : ℝ)/8) ∧ Real.exp ((-1131/57344 : ℝ)/8) ≤ (498768826108473079/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1131/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0437_exp_lower : (459044986294486357/500000000000000000 : ℝ) ≤ Real.exp ((-10938865127433/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938865127433/16000000000000 : ℝ)/8) ≤ (183617994517794543/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938865127433/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0437_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019026148893/1000000000000 : ℝ) ≤ 4*Real.exp (9047/65536 : ℝ)*Real.exp (-mu (radius 7 (1131/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019026148893/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1131/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0437_exp_radius
  have hrNumeric : (980470152631/1000000000000 : ℝ) ≤ Real.exp (-1131/57344 : ℝ) ∧ Real.exp (-1131/57344 : ℝ) ≤ (122558769079/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980470152631/1000000000000 : ℝ) ≤ (radius 7 (1131/8192 : ℝ)) ∧ (radius 7 (1131/8192 : ℝ)) ≤ (122558769079/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1131/8192 : ℝ)) (980470152631/1000000000000 : ℝ) (122558769079/125000000000 : ℝ) (24583492873/125000000000 : ℝ) (19666794299/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1131/8192 : ℝ)) (980470152631/1000000000000 : ℝ) (122558769079/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980470152631/1000000000000 : ℝ) (122558769079/125000000000 : ℝ) (198047015263/200000000000 : ℝ) (247558769079/250000000000 : ℝ) (316859817/320000000 : ℝ) (990186928127/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 1 (198047015263/200000000000 : ℝ) (247558769079/250000000000 : ℝ) (316859817/320000000 : ℝ) (990186928127/1000000000000 : ℝ) (49510550111/50000000000 : ℝ) (495105501111/500000000000 : ℝ) (990211001927/1000000000000 : ℝ) (990211001929/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 2 (49510550111/50000000000 : ℝ) (495105501111/500000000000 : ℝ) (990211001927/1000000000000 : ℝ) (990211001929/1000000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 3 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 4 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 5 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 6 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1131/8192 : ℝ)) 7 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1131/8192 : ℝ))) (24583492873/125000000000 : ℝ) (19666794299/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24583492873/125000000000 : ℝ) (19666794299/100000000000 : ℝ) (149583492873/250000000000 : ℝ) (119666794299/200000000000 : ℝ) (443472595527/1000000000000 : ℝ) (88694519107/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 1 (149583492873/250000000000 : ℝ) (119666794299/200000000000 : ℝ) (443472595527/1000000000000 : ℝ) (88694519107/200000000000 : ℝ) (520903283509/1000000000000 : ℝ) (104180656703/200000000000 : ℝ) (103023243849/200000000000 : ℝ) (128779054813/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 2 (520903283509/1000000000000 : ℝ) (104180656703/200000000000 : ℝ) (103023243849/200000000000 : ℝ) (128779054813/250000000000 : ℝ) (518009751377/1000000000000 : ℝ) (64751218923/125000000000 : ℝ) (4144013359/8000000000 : ℝ) (259000834941/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 3 (518009751377/1000000000000 : ℝ) (64751218923/125000000000 : ℝ) (4144013359/8000000000 : ℝ) (259000834941/500000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710633/1000000000000 : ℝ) (51800571061/100000000000 : ℝ) (259002855309/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 4 (259002855313/500000000000 : ℝ) (518005710633/1000000000000 : ℝ) (51800571061/100000000000 : ℝ) (259002855309/500000000000 : ℝ) (259002855309/500000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 5 (259002855309/500000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 6 (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1131/8192 : ℝ))) 7 (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1131/8192 : ℝ)) hmem 8 (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1131/8192 : ℝ))) hcmem 8 (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1131/8192 : ℝ)) (990211002073/1000000000000 : ℝ) (247552750519/250000000000 : ℝ) (518005710617/1000000000000 : ℝ) (259002855313/500000000000 : ℝ) (164345067019/200000000000 : ℝ) (821725335113/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0437_exp_lower
  have heNumeric : (2019026148893/1000000000000 : ℝ)/4 ≤ Real.exp (-10938865127433/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019026148893/1000000000000 : ℝ)/4 ≤ Real.exp ((9047/65536 : ℝ)-(821725335113/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9047/65536 : ℝ) (1131/8192 : ℝ) (821725335113/1000000000000 : ℝ) (2019026148893/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0438; no trusted numerical premise.
theorem cover7_leaf0438_exp_radius : (997537380409543597/1000000000000000000 : ℝ) ≤ Real.exp ((-9049/458752 : ℝ)/8) ∧ Real.exp ((-9049/458752 : ℝ)/8) ≤ (498768690204771799/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9049/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0438_exp_lower : (183617997658444087/200000000000000000 : ℝ) ≤ Real.exp ((-1367357867261/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367357867261/2000000000000 : ℝ)/8) ≤ (229522497073055109/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367357867261/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0438_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403805285033/200000000000 : ℝ) ≤ 4*Real.exp (1131/8192 : ℝ)*Real.exp (-mu (radius 7 (9049/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403805285033/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9049/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0438_exp_radius
  have hrNumeric : (490234007689/500000000000 : ℝ) ≤ Real.exp (-9049/458752 : ℝ) ∧ Real.exp (-9049/458752 : ℝ) ≤ (980468015379/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490234007689/500000000000 : ℝ) ≤ (radius 7 (9049/65536 : ℝ)) ∧ (radius 7 (9049/65536 : ℝ)) ≤ (980468015379/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9049/65536 : ℝ)) (490234007689/500000000000 : ℝ) (980468015379/1000000000000 : ℝ) (49169649441/250000000000 : ℝ) (19667859777/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9049/65536 : ℝ)) (490234007689/500000000000 : ℝ) (980468015379/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490234007689/500000000000 : ℝ) (980468015379/1000000000000 : ℝ) (990234007689/1000000000000 : ℝ) (99023400769/100000000000 : ℝ) (247546462227/250000000000 : ℝ) (990185848909/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 1 (990234007689/1000000000000 : ℝ) (99023400769/100000000000 : ℝ) (247546462227/250000000000 : ℝ) (990185848909/1000000000000 : ℝ) (495104964149/500000000000 : ℝ) (9902099283/10000000000 : ℝ) (198041985601/200000000000 : ℝ) (990209928007/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 2 (495104964149/500000000000 : ℝ) (9902099283/10000000000 : ℝ) (198041985601/200000000000 : ℝ) (990209928007/1000000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 3 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 4 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 5 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 6 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9049/65536 : ℝ)) 7 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9049/65536 : ℝ))) (49169649441/250000000000 : ℝ) (19667859777/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49169649441/250000000000 : ℝ) (19667859777/100000000000 : ℝ) (299169649441/500000000000 : ℝ) (119667859777/200000000000 : ℝ) (22174230413/50000000000 : ℝ) (110871152067/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 1 (299169649441/500000000000 : ℝ) (119667859777/200000000000 : ℝ) (22174230413/50000000000 : ℝ) (110871152067/250000000000 : ℝ) (520911953571/1000000000000 : ℝ) (520911953577/1000000000000 : ℝ) (515125489149/1000000000000 : ℝ) (128781372289/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 2 (520911953571/1000000000000 : ℝ) (520911953577/1000000000000 : ℝ) (515125489149/1000000000000 : ℝ) (128781372289/250000000000 : ℝ) (6475234017/12500000000 : ℝ) (518018721367/1000000000000 : ℝ) (518010641673/1000000000000 : ℝ) (6475133021/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 3 (6475234017/12500000000 : ℝ) (518018721367/1000000000000 : ℝ) (518010641673/1000000000000 : ℝ) (6475133021/12500000000 : ℝ) (129503670379/250000000000 : ℝ) (129503670381/250000000000 : ℝ) (1036029363/2000000000 : ℝ) (129503670377/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 4 (129503670379/250000000000 : ℝ) (129503670381/250000000000 : ℝ) (1036029363/2000000000 : ℝ) (129503670377/250000000000 : ℝ) (129503670377/250000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 5 (129503670377/250000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 6 (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9049/65536 : ℝ))) 7 (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9049/65536 : ℝ)) hmem 8 (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9049/65536 : ℝ))) hcmem 8 (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9049/65536 : ℝ)) (990209928151/1000000000000 : ℝ) (495104964077/500000000000 : ℝ) (518014681507/1000000000000 : ℝ) (129503670379/250000000000 : ℝ) (16434809141/20000000000 : ℝ) (205435114267/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0438_exp_lower
  have heNumeric : (403805285033/200000000000 : ℝ)/4 ≤ Real.exp (-1367357867261/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403805285033/200000000000 : ℝ)/4 ≤ Real.exp ((1131/8192 : ℝ)-(205435114267/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1131/8192 : ℝ) (9049/65536 : ℝ) (205435114267/250000000000 : ℝ) (403805285033/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0439; no trusted numerical premise.
theorem cover7_leaf0439_exp_radius : (498768554301107549/500000000000000000 : ℝ) ≤ Real.exp ((-4525/229376 : ℝ)/8) ∧ Real.exp ((-4525/229376 : ℝ)/8) ≤ (997537108602215099/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4525/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0439_exp_lower : (18361800082454773/20000000000000000 : ℝ) ≤ Real.exp ((-10938860730999/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938860730999/16000000000000 : ℝ)/8) ≤ (918090004122738651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938860730999/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0439_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504756675919/250000000000 : ℝ) ≤ 4*Real.exp (9049/65536 : ℝ)*Real.exp (-mu (radius 7 (4525/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504756675919/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4525/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0439_exp_radius
  have hrNumeric : (980465878129/1000000000000 : ℝ) ≤ Real.exp (-4525/229376 : ℝ) ∧ Real.exp (-4525/229376 : ℝ) ≤ (98046587813/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980465878129/1000000000000 : ℝ) ≤ (radius 7 (4525/32768 : ℝ)) ∧ (radius 7 (4525/32768 : ℝ)) ≤ (98046587813/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4525/32768 : ℝ)) (980465878129/1000000000000 : ℝ) (98046587813/100000000000 : ℝ) (49172312981/250000000000 : ℝ) (19668925193/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4525/32768 : ℝ)) (980465878129/1000000000000 : ℝ) (98046587813/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980465878129/1000000000000 : ℝ) (98046587813/100000000000 : ℝ) (123779117383/125000000000 : ℝ) (198046587813/200000000000 : ℝ) (990184769691/1000000000000 : ℝ) (990184769693/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 1 (123779117383/125000000000 : ℝ) (198046587813/200000000000 : ℝ) (990184769691/1000000000000 : ℝ) (990184769693/1000000000000 : ℝ) (990208854377/1000000000000 : ℝ) (990208854379/1000000000000 : ℝ) (247552213521/250000000000 : ℝ) (990208854087/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 2 (990208854377/1000000000000 : ℝ) (990208854379/1000000000000 : ℝ) (247552213521/250000000000 : ℝ) (990208854087/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 3 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 4 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 5 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 6 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4525/32768 : ℝ)) 7 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4525/32768 : ℝ))) (49172312981/250000000000 : ℝ) (19668925193/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49172312981/250000000000 : ℝ) (19668925193/100000000000 : ℝ) (299172312981/500000000000 : ℝ) (119668925193/200000000000 : ℝ) (443496619969/1000000000000 : ℝ) (55437077497/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 1 (299172312981/500000000000 : ℝ) (119668925193/200000000000 : ℝ) (443496619969/1000000000000 : ℝ) (55437077497/125000000000 : ℝ) (104184124593/200000000000 : ℝ) (520920622971/1000000000000 : ℝ) (257567379141/500000000000 : ℝ) (32195922393/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 2 (104184124593/200000000000 : ℝ) (520920622971/1000000000000 : ℝ) (257567379141/500000000000 : ℝ) (32195922393/62500000000 : ℝ) (518027690623/1000000000000 : ℝ) (51802769063/100000000000 : ℝ) (518019612751/1000000000000 : ℝ) (259009806379/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 3 (518027690623/1000000000000 : ℝ) (51802769063/100000000000 : ℝ) (518019612751/1000000000000 : ℝ) (259009806379/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825847/500000000000 : ℝ) (518023651671/1000000000000 : ℝ) (518023651679/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 4 (518023651687/1000000000000 : ℝ) (259011825847/500000000000 : ℝ) (518023651671/1000000000000 : ℝ) (518023651679/1000000000000 : ℝ) (518023651679/1000000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 5 (518023651679/1000000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 6 (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4525/32768 : ℝ))) 7 (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4525/32768 : ℝ)) hmem 8 (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4525/32768 : ℝ))) hcmem 8 (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4525/32768 : ℝ)) (99020885423/100000000000 : ℝ) (990208854233/1000000000000 : ℝ) (259011825839/500000000000 : ℝ) (518023651687/1000000000000 : ℝ) (102719447237/125000000000 : ℝ) (410877788957/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0439_exp_lower
  have heNumeric : (504756675919/250000000000 : ℝ)/4 ≤ Real.exp (-10938860730999/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504756675919/250000000000 : ℝ)/4 ≤ Real.exp ((9049/65536 : ℝ)-(410877788957/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9049/65536 : ℝ) (4525/32768 : ℝ) (410877788957/500000000000 : ℝ) (504756675919/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0440; no trusted numerical premise.
theorem cover7_leaf0440_exp_radius : (498768418397480331/500000000000000000 : ℝ) ≤ Real.exp ((-1293/65536 : ℝ)/8) ∧ Real.exp ((-1293/65536 : ℝ)/8) ≤ (997536836794960663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1293/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0440_exp_lower : (918090020082248787/1000000000000000000 : ℝ) ≤ Real.exp ((-5469429252963/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469429252963/8000000000000 : ℝ)/8) ≤ (229522505020562197/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469429252963/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0440_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252378373057/125000000000 : ℝ) ≤ 4*Real.exp (4525/32768 : ℝ)*Real.exp (-mu (radius 7 (9051/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (252378373057/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9051/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0440_exp_radius
  have hrNumeric : (490231870443/500000000000 : ℝ) ≤ Real.exp (-1293/65536 : ℝ) ∧ Real.exp (-1293/65536 : ℝ) ≤ (980463740887/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490231870443/500000000000 : ℝ) ≤ (radius 7 (9051/65536 : ℝ)) ∧ (radius 7 (9051/65536 : ℝ)) ≤ (980463740887/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9051/65536 : ℝ)) (490231870443/500000000000 : ℝ) (980463740887/1000000000000 : ℝ) (98349952727/500000000000 : ℝ) (9834995273/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9051/65536 : ℝ)) (490231870443/500000000000 : ℝ) (980463740887/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490231870443/500000000000 : ℝ) (980463740887/1000000000000 : ℝ) (990231870443/1000000000000 : ℝ) (247557967611/250000000000 : ℝ) (247545922619/250000000000 : ℝ) (495091845239/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 1 (990231870443/1000000000000 : ℝ) (247557967611/250000000000 : ℝ) (247545922619/250000000000 : ℝ) (495091845239/500000000000 : ℝ) (990207780459/1000000000000 : ℝ) (990207780461/1000000000000 : ℝ) (495103890083/500000000000 : ℝ) (123775972521/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 2 (990207780459/1000000000000 : ℝ) (990207780461/1000000000000 : ℝ) (495103890083/500000000000 : ℝ) (123775972521/125000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 3 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 4 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 5 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 6 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9051/65536 : ℝ)) 7 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9051/65536 : ℝ))) (98349952727/500000000000 : ℝ) (9834995273/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98349952727/500000000000 : ℝ) (9834995273/50000000000 : ℝ) (598349952727/1000000000000 : ℝ) (59834995273/100000000000 : ℝ) (221754315321/500000000000 : ℝ) (443508630649/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 1 (598349952727/1000000000000 : ℝ) (59834995273/100000000000 : ℝ) (221754315321/500000000000 : ℝ) (443508630649/1000000000000 : ℝ) (130232322921/250000000000 : ℝ) (52092929169/100000000000 : ℝ) (103028805327/200000000000 : ℝ) (257572013321/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 2 (130232322921/250000000000 : ℝ) (52092929169/100000000000 : ℝ) (103028805327/200000000000 : ℝ) (257572013321/500000000000 : ℝ) (518036659159/1000000000000 : ℝ) (259018329583/500000000000 : ℝ) (518028583101/1000000000000 : ℝ) (518028583109/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 3 (518036659159/1000000000000 : ℝ) (259018329583/500000000000 : ℝ) (518028583101/1000000000000 : ℝ) (518028583109/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (259016310569/500000000000 : ℝ) (259016310557/500000000000 : ℝ) (259016310561/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 4 (51803262113/100000000000 : ℝ) (259016310569/500000000000 : ℝ) (259016310557/500000000000 : ℝ) (259016310561/500000000000 : ℝ) (259016310561/500000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 5 (259016310561/500000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 6 (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9051/65536 : ℝ))) 7 (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9051/65536 : ℝ)) hmem 8 (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9051/65536 : ℝ))) hcmem 8 (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9051/65536 : ℝ)) (123775972539/125000000000 : ℝ) (198041556063/200000000000 : ℝ) (518032621121/1000000000000 : ℝ) (51803262113/100000000000 : ℝ) (410885348809/500000000000 : ℝ) (205442674409/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0440_exp_lower
  have heNumeric : (252378373057/125000000000 : ℝ)/4 ≤ Real.exp (-5469429252963/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252378373057/125000000000 : ℝ)/4 ≤ Real.exp ((4525/32768 : ℝ)-(205442674409/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4525/32768 : ℝ) (9051/65536 : ℝ) (205442674409/250000000000 : ℝ) (252378373057/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0441; no trusted numerical premise.
theorem cover7_leaf0441_exp_radius : (997536564987780287/1000000000000000000 : ℝ) ≤ Real.exp ((-2263/114688 : ℝ)/8) ∧ Real.exp ((-2263/114688 : ℝ)/8) ≤ (15586508827934067/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2263/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0441_exp_lower : (918090036169029433/1000000000000000000 : ℝ) ≤ Real.exp ((-10938856263109/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938856263109/16000000000000 : ℝ)/8) ≤ (459045018084514717/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938856263109/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0441_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80761090699/40000000000 : ℝ) ≤ 4*Real.exp (9051/65536 : ℝ)*Real.exp (-mu (radius 7 (2263/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (80761090699/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2263/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0441_exp_radius
  have hrNumeric : (980461603647/1000000000000 : ℝ) ≤ Real.exp (-2263/114688 : ℝ) ∧ Real.exp (-2263/114688 : ℝ) ≤ (15319712557/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980461603647/1000000000000 : ℝ) ≤ (radius 7 (2263/16384 : ℝ)) ∧ (radius 7 (2263/16384 : ℝ)) ≤ (15319712557/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2263/16384 : ℝ)) (980461603647/1000000000000 : ℝ) (15319712557/15625000000 : ℝ) (49177639591/250000000000 : ℝ) (19671055837/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2263/16384 : ℝ)) (980461603647/1000000000000 : ℝ) (15319712557/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980461603647/1000000000000 : ℝ) (15319712557/15625000000 : ℝ) (990230801823/1000000000000 : ℝ) (30944712557/31250000000 : ℝ) (495091305631/500000000000 : ℝ) (15471603301/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 1 (990230801823/1000000000000 : ℝ) (30944712557/31250000000 : ℝ) (495091305631/500000000000 : ℝ) (15471603301/15625000000 : ℝ) (495103353271/500000000000 : ℝ) (61887919159/62500000000 : ℝ) (990206706249/1000000000000 : ℝ) (990206706251/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 2 (495103353271/500000000000 : ℝ) (61887919159/62500000000 : ℝ) (990206706249/1000000000000 : ℝ) (990206706251/1000000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 3 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 4 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 5 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 6 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2263/16384 : ℝ)) 7 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2263/16384 : ℝ))) (49177639591/250000000000 : ℝ) (19671055837/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49177639591/250000000000 : ℝ) (19671055837/100000000000 : ℝ) (299177639591/500000000000 : ℝ) (119671055837/200000000000 : ℝ) (44352064029/100000000000 : ℝ) (221760320149/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 1 (299177639591/500000000000 : ℝ) (119671055837/200000000000 : ℝ) (44352064029/100000000000 : ℝ) (221760320149/500000000000 : ℝ) (65117244967/125000000000 : ℝ) (260468979871/500000000000 : ℝ) (257576647109/500000000000 : ℝ) (32197080889/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 2 (65117244967/125000000000 : ℝ) (260468979871/500000000000 : ℝ) (257576647109/500000000000 : ℝ) (32197080889/62500000000 : ℝ) (518045626977/1000000000000 : ℝ) (518045626983/1000000000000 : ℝ) (129509388183/250000000000 : ℝ) (518037552739/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 3 (518045626977/1000000000000 : ℝ) (518045626983/1000000000000 : ℝ) (129509388183/250000000000 : ℝ) (518037552739/1000000000000 : ℝ) (259020794927/500000000000 : ℝ) (518041589861/1000000000000 : ℝ) (259020794919/500000000000 : ℝ) (259020794923/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 4 (259020794927/500000000000 : ℝ) (518041589861/1000000000000 : ℝ) (259020794919/500000000000 : ℝ) (259020794923/500000000000 : ℝ) (259020794923/500000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 5 (259020794923/500000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 6 (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2263/16384 : ℝ))) 7 (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2263/16384 : ℝ)) hmem 8 (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2263/16384 : ℝ))) hcmem 8 (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2263/16384 : ℝ)) (198041341279/200000000000 : ℝ) (495103353199/500000000000 : ℝ) (103608317969/200000000000 : ℝ) (259020794927/500000000000 : ℝ) (821785816231/1000000000000 : ℝ) (821785816249/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0441_exp_lower
  have heNumeric : (80761090699/40000000000 : ℝ)/4 ≤ Real.exp (-10938856263109/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80761090699/40000000000 : ℝ)/4 ≤ Real.exp ((9051/65536 : ℝ)-(821785816249/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9051/65536 : ℝ) (2263/16384 : ℝ) (821785816249/1000000000000 : ℝ) (80761090699/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0442; no trusted numerical premise.
theorem cover7_leaf0442_exp_radius : (997536293180673973/1000000000000000000 : ℝ) ≤ Real.exp ((-9053/458752 : ℝ)/8) ∧ Real.exp ((-9053/458752 : ℝ)/8) ≤ (498768146590336987/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9053/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0442_exp_lower : (229522513095827529/250000000000000000 : ℝ) ≤ Real.exp ((-2734713500629/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734713500629/4000000000000 : ℝ)/8) ≤ (918090052383310117/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734713500629/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0442_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019027552737/1000000000000 : ℝ) ≤ 4*Real.exp (2263/16384 : ℝ)*Real.exp (-mu (radius 7 (9053/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019027552737/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9053/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0442_exp_radius
  have hrNumeric : (245114866603/250000000000 : ℝ) ≤ Real.exp (-9053/458752 : ℝ) ∧ Real.exp (-9053/458752 : ℝ) ≤ (980459466413/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245114866603/250000000000 : ℝ) ≤ (radius 7 (9053/65536 : ℝ)) ∧ (radius 7 (9053/65536 : ℝ)) ≤ (980459466413/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9053/65536 : ℝ)) (245114866603/250000000000 : ℝ) (980459466413/1000000000000 : ℝ) (196721210653/1000000000000 : ℝ) (196721210659/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9053/65536 : ℝ)) (245114866603/250000000000 : ℝ) (980459466413/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245114866603/250000000000 : ℝ) (980459466413/1000000000000 : ℝ) (495114866603/500000000000 : ℝ) (990229733207/1000000000000 : ℝ) (990181532049/1000000000000 : ℝ) (990181532051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 1 (495114866603/500000000000 : ℝ) (990229733207/1000000000000 : ℝ) (990181532049/1000000000000 : ℝ) (990181532051/1000000000000 : ℝ) (990205632627/1000000000000 : ℝ) (990205632629/1000000000000 : ℝ) (495102816167/500000000000 : ℝ) (61887852021/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 2 (990205632627/1000000000000 : ℝ) (990205632629/1000000000000 : ℝ) (495102816167/500000000000 : ℝ) (61887852021/62500000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 3 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 4 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 5 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 6 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9053/65536 : ℝ)) 7 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9053/65536 : ℝ))) (196721210653/1000000000000 : ℝ) (196721210659/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196721210653/1000000000000 : ℝ) (196721210659/1000000000000 : ℝ) (299180302663/500000000000 : ℝ) (59836060533/100000000000 : ℝ) (221766324457/500000000000 : ℝ) (221766324461/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 1 (299180302663/500000000000 : ℝ) (59836060533/100000000000 : ℝ) (221766324457/500000000000 : ℝ) (221766324461/500000000000 : ℝ) (6511832839/12500000000 : ℝ) (260473313563/500000000000 : ℝ) (515162561029/1000000000000 : ℝ) (128790640259/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 2 (6511832839/12500000000 : ℝ) (260473313563/500000000000 : ℝ) (515162561029/1000000000000 : ℝ) (128790640259/250000000000 : ℝ) (259027297037/500000000000 : ℝ) (518054594081/1000000000000 : ℝ) (518046521643/1000000000000 : ℝ) (10360930433/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 3 (259027297037/500000000000 : ℝ) (518054594081/1000000000000 : ℝ) (518046521643/1000000000000 : ℝ) (10360930433/20000000000 : ℝ) (259025278929/500000000000 : ℝ) (259025278933/500000000000 : ℝ) (259025278921/500000000000 : ℝ) (10361011157/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 4 (259025278929/500000000000 : ℝ) (259025278933/500000000000 : ℝ) (259025278921/500000000000 : ℝ) (10361011157/20000000000 : ℝ) (10361011157/20000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 5 (10361011157/20000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 6 (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9053/65536 : ℝ))) 7 (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9053/65536 : ℝ)) hmem 8 (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9053/65536 : ℝ))) hcmem 8 (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9053/65536 : ℝ)) (6188785203/6250000000 : ℝ) (990205632483/1000000000000 : ℝ) (518050557849/1000000000000 : ℝ) (259025278929/500000000000 : ℝ) (410900466867/500000000000 : ℝ) (821800933751/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0442_exp_lower
  have heNumeric : (2019027552737/1000000000000 : ℝ)/4 ≤ Real.exp (-2734713500629/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019027552737/1000000000000 : ℝ)/4 ≤ Real.exp ((2263/16384 : ℝ)-(821800933751/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2263/16384 : ℝ) (9053/65536 : ℝ) (821800933751/1000000000000 : ℝ) (2019027552737/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0443; no trusted numerical premise.
theorem cover7_leaf0443_exp_radius : (997536021373641721/1000000000000000000 : ℝ) ≤ Real.exp ((-4527/229376 : ℝ)/8) ∧ Real.exp ((-4527/229376 : ℝ)/8) ≤ (498768010686820861/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4527/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0443_exp_lower : (183618013745224739/200000000000000000 : ℝ) ≤ Real.exp ((-10938851724003/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938851724003/16000000000000 : ℝ)/8) ≤ (57380629295382731/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938851724003/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0443_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019027840261/1000000000000 : ℝ) ≤ 4*Real.exp (9053/65536 : ℝ)*Real.exp (-mu (radius 7 (4527/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019027840261/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4527/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0443_exp_radius
  have hrNumeric : (980457329183/1000000000000 : ℝ) ≤ Real.exp (-4527/229376 : ℝ) ∧ Real.exp (-4527/229376 : ℝ) ≤ (30639291537/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980457329183/1000000000000 : ℝ) ≤ (radius 7 (4527/32768 : ℝ)) ∧ (radius 7 (4527/32768 : ℝ)) ≤ (30639291537/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4527/32768 : ℝ)) (980457329183/1000000000000 : ℝ) (30639291537/31250000000 : ℝ) (196731862313/1000000000000 : ℝ) (196731862319/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4527/32768 : ℝ)) (980457329183/1000000000000 : ℝ) (30639291537/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980457329183/1000000000000 : ℝ) (30639291537/31250000000 : ℝ) (990228664591/1000000000000 : ℝ) (61889291537/62500000000 : ℝ) (495090226419/500000000000 : ℝ) (990180452839/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 1 (990228664591/1000000000000 : ℝ) (61889291537/62500000000 : ℝ) (495090226419/500000000000 : ℝ) (990180452839/1000000000000 : ℝ) (495102279357/500000000000 : ℝ) (247551139679/250000000000 : ℝ) (990204558421/1000000000000 : ℝ) (990204558423/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 2 (495102279357/500000000000 : ℝ) (247551139679/250000000000 : ℝ) (990204558421/1000000000000 : ℝ) (990204558423/1000000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 3 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 4 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 5 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 6 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4527/32768 : ℝ)) 7 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4527/32768 : ℝ))) (196731862313/1000000000000 : ℝ) (196731862319/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196731862313/1000000000000 : ℝ) (196731862319/1000000000000 : ℝ) (149591482789/250000000000 : ℝ) (14959148279/25000000000 : ℝ) (443544656503/1000000000000 : ℝ) (443544656511/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 1 (149591482789/250000000000 : ℝ) (14959148279/25000000000 : ℝ) (443544656503/1000000000000 : ℝ) (443544656511/1000000000000 : ℝ) (520955293829/1000000000000 : ℝ) (130238823459/250000000000 : ℝ) (515171827061/1000000000000 : ℝ) (128792956767/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 2 (520955293829/1000000000000 : ℝ) (130238823459/250000000000 : ℝ) (515171827061/1000000000000 : ℝ) (128792956767/250000000000 : ℝ) (103612712089/200000000000 : ℝ) (129515890113/250000000000 : ℝ) (259027744913/500000000000 : ℝ) (259027744917/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 3 (103612712089/200000000000 : ℝ) (129515890113/250000000000 : ℝ) (259027744913/500000000000 : ℝ) (259027744917/500000000000 : ℝ) (103611905027/200000000000 : ℝ) (518059525143/1000000000000 : ℝ) (518059525119/1000000000000 : ℝ) (64757440641/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 4 (103611905027/200000000000 : ℝ) (518059525143/1000000000000 : ℝ) (518059525119/1000000000000 : ℝ) (64757440641/125000000000 : ℝ) (518059525127/1000000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 5 (518059525127/1000000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 6 (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4527/32768 : ℝ))) 7 (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4527/32768 : ℝ)) hmem 8 (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4527/32768 : ℝ))) hcmem 8 (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4527/32768 : ℝ)) (990204558567/1000000000000 : ℝ) (99020455857/100000000000 : ℝ) (259029762563/500000000000 : ℝ) (32378720321/62500000000 : ℝ) (410908025057/500000000000 : ℝ) (821816050133/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0443_exp_lower
  have heNumeric : (2019027840261/1000000000000 : ℝ)/4 ≤ Real.exp (-10938851724003/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019027840261/1000000000000 : ℝ)/4 ≤ Real.exp ((9053/65536 : ℝ)-(821816050133/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9053/65536 : ℝ) (4527/32768 : ℝ) (821816050133/1000000000000 : ℝ) (2019027840261/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0444; no trusted numerical premise.
theorem cover7_leaf0444_exp_radius : (997535749566683531/1000000000000000000 : ℝ) ≤ Real.exp ((-9055/458752 : ℝ)/8) ∧ Real.exp ((-9055/458752 : ℝ)/8) ≤ (249383937391670883/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9055/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0444_exp_lower : (459045042598218663/500000000000000000 : ℝ) ≤ Real.exp ((-5469424713857/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469424713857/8000000000000 : ℝ)/8) ≤ (918090085196437327/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469424713857/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0444_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504757032507/250000000000 : ℝ) ≤ 4*Real.exp (4527/32768 : ℝ)*Real.exp (-mu (radius 7 (9055/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504757032507/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9055/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0444_exp_radius
  have hrNumeric : (490227595979/500000000000 : ℝ) ≤ Real.exp (-9055/458752 : ℝ) ∧ Real.exp (-9055/458752 : ℝ) ≤ (980455191959/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490227595979/500000000000 : ℝ) ≤ (radius 7 (9055/65536 : ℝ)) ∧ (radius 7 (9055/65536 : ℝ)) ≤ (980455191959/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9055/65536 : ℝ)) (490227595979/500000000000 : ℝ) (980455191959/1000000000000 : ℝ) (196742513353/1000000000000 : ℝ) (196742513359/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9055/65536 : ℝ)) (490227595979/500000000000 : ℝ) (980455191959/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490227595979/500000000000 : ℝ) (980455191959/1000000000000 : ℝ) (990227595979/1000000000000 : ℝ) (49511379799/50000000000 : ℝ) (990179373627/1000000000000 : ℝ) (990179373629/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 1 (990227595979/1000000000000 : ℝ) (49511379799/50000000000 : ℝ) (990179373627/1000000000000 : ℝ) (990179373629/1000000000000 : ℝ) (990203484803/1000000000000 : ℝ) (198040696961/200000000000 : ℝ) (990203484509/1000000000000 : ℝ) (990203484511/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 2 (990203484803/1000000000000 : ℝ) (198040696961/200000000000 : ℝ) (990203484509/1000000000000 : ℝ) (990203484511/1000000000000 : ℝ) (61887717791/62500000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 3 (61887717791/62500000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 4 (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 5 (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 6 (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9055/65536 : ℝ)) 7 (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9055/65536 : ℝ))) (196742513353/1000000000000 : ℝ) (196742513359/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196742513353/1000000000000 : ℝ) (196742513359/1000000000000 : ℝ) (149592814169/250000000000 : ℝ) (14959281417/25000000000 : ℝ) (443556663069/1000000000000 : ℝ) (110889165769/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 1 (149592814169/250000000000 : ℝ) (14959281417/25000000000 : ℝ) (443556663069/1000000000000 : ℝ) (110889165769/250000000000 : ℝ) (8140061873/15625000000 : ℝ) (260481979939/500000000000 : ℝ) (515181092323/1000000000000 : ℝ) (51518109233/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 2 (8140061873/15625000000 : ℝ) (260481979939/500000000000 : ℝ) (515181092323/1000000000000 : ℝ) (51518109233/100000000000 : ℝ) (518072526097/1000000000000 : ℝ) (64759065763/125000000000 : ℝ) (51806445729/100000000000 : ℝ) (259032228649/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 3 (518072526097/1000000000000 : ℝ) (64759065763/125000000000 : ℝ) (51806445729/100000000000 : ℝ) (259032228649/500000000000 : ℝ) (518068491693/1000000000000 : ℝ) (518068491701/1000000000000 : ℝ) (518068491677/1000000000000 : ℝ) (259034245843/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 4 (518068491693/1000000000000 : ℝ) (518068491701/1000000000000 : ℝ) (518068491677/1000000000000 : ℝ) (259034245843/500000000000 : ℝ) (103613698337/200000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 5 (103613698337/200000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 6 (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9055/65536 : ℝ))) 7 (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9055/65536 : ℝ)) hmem 8 (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9055/65536 : ℝ))) hcmem 8 (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9055/65536 : ℝ)) (198040696931/200000000000 : ℝ) (495101742329/500000000000 : ℝ) (129517122921/250000000000 : ℝ) (259034245847/500000000000 : ℝ) (164366233077/200000000000 : ℝ) (205457791351/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0444_exp_lower
  have heNumeric : (504757032507/250000000000 : ℝ)/4 ≤ Real.exp (-5469424713857/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504757032507/250000000000 : ℝ)/4 ≤ Real.exp ((4527/32768 : ℝ)-(205457791351/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4527/32768 : ℝ) (9055/65536 : ℝ) (205457791351/250000000000 : ℝ) (504757032507/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0445; no trusted numerical premise.
theorem cover7_leaf0445_exp_radius : (498767738879899701/500000000000000000 : ℝ) ≤ Real.exp ((-283/14336 : ℝ)/8) ∧ Real.exp ((-283/14336 : ℝ)/8) ≤ (997535477759799403/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-283/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0445_exp_lower : (918090101793906731/1000000000000000000 : ℝ) ≤ Real.exp ((-10938847113697/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938847113697/16000000000000 : ℝ)/8) ≤ (229522525448476683/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938847113697/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0445_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126189276377/62500000000 : ℝ) ≤ 4*Real.exp (9055/65536 : ℝ)*Real.exp (-mu (radius 7 (283/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (126189276377/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (283/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0445_exp_radius
  have hrNumeric : (980453054737/1000000000000 : ℝ) ≤ Real.exp (-283/14336 : ℝ) ∧ Real.exp (-283/14336 : ℝ) ≤ (490226527369/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980453054737/1000000000000 : ℝ) ≤ (radius 7 (283/2048 : ℝ)) ∧ (radius 7 (283/2048 : ℝ)) ≤ (490226527369/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (283/2048 : ℝ)) (980453054737/1000000000000 : ℝ) (490226527369/500000000000 : ℝ) (196753163773/1000000000000 : ℝ) (196753163779/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (283/2048 : ℝ)) (980453054737/1000000000000 : ℝ) (490226527369/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (283/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980453054737/1000000000000 : ℝ) (490226527369/500000000000 : ℝ) (123778315921/125000000000 : ℝ) (990226527369/1000000000000 : ℝ) (495089147209/500000000000 : ℝ) (990178294419/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (283/2048 : ℝ)) 1 (123778315921/125000000000 : ℝ) (990226527369/1000000000000 : ℝ) (495089147209/500000000000 : ℝ) (990178294419/1000000000000 : ℝ) (990202410893/1000000000000 : ℝ) (495101205447/500000000000 : ℝ) (990202410599/1000000000000 : ℝ) (990202410601/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (283/2048 : ℝ)) 2 (990202410893/1000000000000 : ℝ) (495101205447/500000000000 : ℝ) (990202410599/1000000000000 : ℝ) (990202410601/1000000000000 : ℝ) (495101205373/500000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (283/2048 : ℝ)) 3 (495101205373/500000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (283/2048 : ℝ)) 4 (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (283/2048 : ℝ)) 5 (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (283/2048 : ℝ)) 6 (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (283/2048 : ℝ)) 7 (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (283/2048 : ℝ))) (196753163773/1000000000000 : ℝ) (196753163779/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196753163773/1000000000000 : ℝ) (196753163779/1000000000000 : ℝ) (299188290943/500000000000 : ℝ) (59837658189/100000000000 : ℝ) (44356866861/100000000000 : ℝ) (221784334309/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 1 (299188290943/500000000000 : ℝ) (59837658189/100000000000 : ℝ) (44356866861/100000000000 : ℝ) (221784334309/500000000000 : ℝ) (16280394539/31250000000 : ℝ) (260486312627/500000000000 : ℝ) (257595178407/500000000000 : ℝ) (515190356821/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 2 (16280394539/31250000000 : ℝ) (260486312627/500000000000 : ℝ) (257595178407/500000000000 : ℝ) (515190356821/1000000000000 : ℝ) (518081491031/1000000000000 : ℝ) (259040745519/500000000000 : ℝ) (103614684807/200000000000 : ℝ) (259036712021/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 3 (518081491031/1000000000000 : ℝ) (259040745519/500000000000 : ℝ) (103614684807/200000000000 : ℝ) (259036712021/500000000000 : ℝ) (518077457533/1000000000000 : ℝ) (25903872877/50000000000 : ℝ) (518077457517/1000000000000 : ℝ) (20723098301/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 4 (518077457533/1000000000000 : ℝ) (25903872877/50000000000 : ℝ) (518077457517/1000000000000 : ℝ) (20723098301/40000000000 : ℝ) (20723098301/40000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 5 (20723098301/40000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 6 (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (283/2048 : ℝ))) 7 (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (283/2048 : ℝ)) hmem 8 (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (283/2048 : ℝ))) hcmem 8 (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (283/2048 : ℝ)) (198040482149/200000000000 : ℝ) (247550602687/250000000000 : ℝ) (129519364381/250000000000 : ℝ) (518077457533/1000000000000 : ℝ) (821846279549/1000000000000 : ℝ) (821846279567/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0445_exp_lower
  have heNumeric : (126189276377/62500000000 : ℝ)/4 ≤ Real.exp (-10938847113697/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126189276377/62500000000 : ℝ)/4 ≤ Real.exp ((9055/65536 : ℝ)-(821846279567/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9055/65536 : ℝ) (283/2048 : ℝ) (821846279567/1000000000000 : ℝ) (126189276377/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0446; no trusted numerical premise.
theorem cover7_leaf0446_exp_radius : (199507041190597867/200000000000000000 : ℝ) ≤ Real.exp ((-9057/458752 : ℝ)/8) ∧ Real.exp ((-9057/458752 : ℝ)/8) ≤ (124691900744123667/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9057/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0446_exp_lower : (918090118519335247/1000000000000000000 : ℝ) ≤ Real.exp ((-136735559773/200000000000 : ℝ)/8) ∧ Real.exp ((-136735559773/200000000000 : ℝ)/8) ≤ (57380632407458453/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136735559773/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0446_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (7886830923/3906250000 : ℝ) ≤ 4*Real.exp (283/2048 : ℝ)*Real.exp (-mu (radius 7 (9057/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (7886830923/3906250000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9057/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0446_exp_radius
  have hrNumeric : (980450917521/1000000000000 : ℝ) ≤ Real.exp (-9057/458752 : ℝ) ∧ Real.exp (-9057/458752 : ℝ) ≤ (490225458761/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980450917521/1000000000000 : ℝ) ≤ (radius 7 (9057/65536 : ℝ)) ∧ (radius 7 (9057/65536 : ℝ)) ≤ (490225458761/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9057/65536 : ℝ)) (980450917521/1000000000000 : ℝ) (490225458761/500000000000 : ℝ) (196763813569/1000000000000 : ℝ) (7870552543/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9057/65536 : ℝ)) (980450917521/1000000000000 : ℝ) (490225458761/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980450917521/1000000000000 : ℝ) (490225458761/500000000000 : ℝ) (24755636469/25000000000 : ℝ) (990225458761/1000000000000 : ℝ) (990177215209/1000000000000 : ℝ) (990177215211/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 1 (24755636469/25000000000 : ℝ) (990225458761/1000000000000 : ℝ) (990177215209/1000000000000 : ℝ) (990177215211/1000000000000 : ℝ) (123775167123/125000000000 : ℝ) (495100668493/500000000000 : ℝ) (99020133669/100000000000 : ℝ) (990201336693/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 2 (123775167123/125000000000 : ℝ) (495100668493/500000000000 : ℝ) (99020133669/100000000000 : ℝ) (990201336693/1000000000000 : ℝ) (990201336837/1000000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 3 (990201336837/1000000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 4 (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 5 (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 6 (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9057/65536 : ℝ)) 7 (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9057/65536 : ℝ))) (196763813569/1000000000000 : ℝ) (7870552543/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196763813569/1000000000000 : ℝ) (7870552543/40000000000 : ℝ) (18699434587/31250000000 : ℝ) (149595476697/250000000000 : ℝ) (443580673123/1000000000000 : ℝ) (443580673131/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 1 (18699434587/31250000000 : ℝ) (149595476697/250000000000 : ℝ) (443580673123/1000000000000 : ℝ) (443580673131/1000000000000 : ℝ) (520981289953/1000000000000 : ℝ) (13024532249/25000000000 : ℝ) (515199620531/1000000000000 : ℝ) (257599810269/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 2 (520981289953/1000000000000 : ℝ) (13024532249/25000000000 : ℝ) (515199620531/1000000000000 : ℝ) (257599810269/500000000000 : ℝ) (259045227621/500000000000 : ℝ) (518090455249/1000000000000 : ℝ) (518082390057/1000000000000 : ℝ) (103616478013/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 3 (259045227621/500000000000 : ℝ) (518090455249/1000000000000 : ℝ) (518082390057/1000000000000 : ℝ) (103616478013/200000000000 : ℝ) (518086422649/1000000000000 : ℝ) (518086422657/1000000000000 : ℝ) (518086422633/1000000000000 : ℝ) (259043211321/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 4 (518086422649/1000000000000 : ℝ) (518086422657/1000000000000 : ℝ) (518086422633/1000000000000 : ℝ) (259043211321/500000000000 : ℝ) (518086422641/1000000000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 5 (518086422641/1000000000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 6 (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9057/65536 : ℝ))) 7 (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9057/65536 : ℝ)) hmem 8 (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9057/65536 : ℝ))) hcmem 8 (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9057/65536 : ℝ)) (247550334209/250000000000 : ℝ) (24755033421/25000000000 : ℝ) (6476080283/12500000000 : ℝ) (10361728453/20000000000 : ℝ) (164372278519/200000000000 : ℝ) (164372278523/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0446_exp_lower
  have heNumeric : (7886830923/3906250000 : ℝ)/4 ≤ Real.exp (-136735559773/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (7886830923/3906250000 : ℝ)/4 ≤ Real.exp ((283/2048 : ℝ)-(164372278523/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (283/2048 : ℝ) (9057/65536 : ℝ) (164372278523/200000000000 : ℝ) (7886830923/3906250000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0447; no trusted numerical premise.
theorem cover7_leaf0447_exp_radius : (997534934146253329/1000000000000000000 : ℝ) ≤ Real.exp ((-647/32768 : ℝ)/8) ∧ Real.exp ((-647/32768 : ℝ)/8) ≤ (99753493414625333/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-647/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0447_exp_lower : (459045067686476201/500000000000000000 : ℝ) ≤ Real.exp ((-10938842432111/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938842432111/16000000000000 : ℝ)/8) ≤ (918090135372952403/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938842432111/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0447_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009514506399/500000000000 : ℝ) ≤ 4*Real.exp (9057/65536 : ℝ)*Real.exp (-mu (radius 7 (4529/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009514506399/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4529/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0447_exp_radius
  have hrNumeric : (98044878031/100000000000 : ℝ) ≤ Real.exp (-647/32768 : ℝ) ∧ Real.exp (-647/32768 : ℝ) ≤ (980448780311/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98044878031/100000000000 : ℝ) ≤ (radius 7 (4529/32768 : ℝ)) ∧ (radius 7 (4529/32768 : ℝ)) ≤ (980448780311/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4529/32768 : ℝ)) (98044878031/100000000000 : ℝ) (980448780311/1000000000000 : ℝ) (9838723137/50000000000 : ℝ) (98387231373/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4529/32768 : ℝ)) (98044878031/100000000000 : ℝ) (980448780311/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98044878031/100000000000 : ℝ) (980448780311/1000000000000 : ℝ) (198044878031/200000000000 : ℝ) (247556097539/250000000000 : ℝ) (990176136003/1000000000000 : ℝ) (247544034001/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 1 (198044878031/200000000000 : ℝ) (247556097539/250000000000 : ℝ) (990176136003/1000000000000 : ℝ) (247544034001/250000000000 : ℝ) (990200263079/1000000000000 : ℝ) (24755006577/25000000000 : ℝ) (198040052557/200000000000 : ℝ) (990200262787/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 2 (990200263079/1000000000000 : ℝ) (24755006577/25000000000 : ℝ) (198040052557/200000000000 : ℝ) (990200262787/1000000000000 : ℝ) (247550065733/250000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 3 (247550065733/250000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 4 (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 5 (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 6 (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4529/32768 : ℝ)) 7 (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4529/32768 : ℝ))) (9838723137/50000000000 : ℝ) (98387231373/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9838723137/50000000000 : ℝ) (98387231373/500000000000 : ℝ) (59838723137/100000000000 : ℝ) (598387231373/1000000000000 : ℝ) (443592676607/1000000000000 : ℝ) (88718535323/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 1 (59838723137/100000000000 : ℝ) (598387231373/1000000000000 : ℝ) (443592676607/1000000000000 : ℝ) (88718535323/200000000000 : ℝ) (130247488497/250000000000 : ℝ) (260494976997/500000000000 : ℝ) (257604441737/500000000000 : ℝ) (515208883481/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 2 (130247488497/250000000000 : ℝ) (260494976997/500000000000 : ℝ) (257604441737/500000000000 : ℝ) (515208883481/1000000000000 : ℝ) (518099418731/1000000000000 : ℝ) (259049709369/500000000000 : ℝ) (129522838839/250000000000 : ℝ) (129522838841/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 3 (518099418731/1000000000000 : ℝ) (259049709369/500000000000 : ℝ) (129522838839/250000000000 : ℝ) (129522838841/250000000000 : ℝ) (518095387043/1000000000000 : ℝ) (518095387051/1000000000000 : ℝ) (518095387027/1000000000000 : ℝ) (129523846759/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 4 (518095387043/1000000000000 : ℝ) (518095387051/1000000000000 : ℝ) (518095387027/1000000000000 : ℝ) (129523846759/250000000000 : ℝ) (103619077407/200000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 5 (103619077407/200000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 6 (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4529/32768 : ℝ))) 7 (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4529/32768 : ℝ)) hmem 8 (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4529/32768 : ℝ))) hcmem 8 (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4529/32768 : ℝ)) (990200262931/1000000000000 : ℝ) (495100131467/500000000000 : ℝ) (259047693517/500000000000 : ℝ) (129523846761/250000000000 : ℝ) (821876504527/1000000000000 : ℝ) (410938252273/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0447_exp_lower
  have heNumeric : (1009514506399/500000000000 : ℝ)/4 ≤ Real.exp (-10938842432111/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009514506399/500000000000 : ℝ)/4 ≤ Real.exp ((9057/65536 : ℝ)-(410938252273/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9057/65536 : ℝ) (4529/32768 : ℝ) (410938252273/500000000000 : ℝ) (1009514506399/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0448; no trusted numerical premise.
theorem cover7_leaf0448_exp_radius : (124691832792448923/125000000000000000 : ℝ) ≤ Real.exp ((-9059/458752 : ℝ)/8) ∧ Real.exp ((-9059/458752 : ℝ)/8) ≤ (199506932467918277/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9059/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0448_exp_lower : (459045076177264341/500000000000000000 : ℝ) ≤ Real.exp ((-5469420032271/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469420032271/8000000000000 : ℝ)/8) ≤ (918090152354528683/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469420032271/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0448_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475732789/25000000000 : ℝ) ≤ 4*Real.exp (4529/32768 : ℝ)*Real.exp (-mu (radius 7 (9059/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (50475732789/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9059/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0448_exp_radius
  have hrNumeric : (30638957597/31250000000 : ℝ) ≤ Real.exp (-9059/458752 : ℝ) ∧ Real.exp (-9059/458752 : ℝ) ≤ (196089328621/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30638957597/31250000000 : ℝ) ≤ (radius 7 (9059/65536 : ℝ)) ∧ (radius 7 (9059/65536 : ℝ)) ≤ (196089328621/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9059/65536 : ℝ)) (30638957597/31250000000 : ℝ) (196089328621/200000000000 : ℝ) (98392555643/500000000000 : ℝ) (49196277823/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9059/65536 : ℝ)) (30638957597/31250000000 : ℝ) (196089328621/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30638957597/31250000000 : ℝ) (196089328621/200000000000 : ℝ) (61888957597/62500000000 : ℝ) (990223321553/1000000000000 : ℝ) (990175056797/1000000000000 : ℝ) (990175056799/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 1 (61888957597/62500000000 : ℝ) (990223321553/1000000000000 : ℝ) (990175056797/1000000000000 : ℝ) (990175056799/1000000000000 : ℝ) (495099594587/500000000000 : ℝ) (123774898647/125000000000 : ℝ) (12377489861/12500000000 : ℝ) (495099594441/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 2 (495099594587/500000000000 : ℝ) (123774898647/125000000000 : ℝ) (12377489861/12500000000 : ℝ) (495099594441/500000000000 : ℝ) (990199189027/1000000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 3 (990199189027/1000000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 4 (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 5 (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 6 (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9059/65536 : ℝ)) 7 (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9059/65536 : ℝ))) (98392555643/500000000000 : ℝ) (49196277823/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98392555643/500000000000 : ℝ) (49196277823/250000000000 : ℝ) (598392555643/1000000000000 : ℝ) (299196277823/500000000000 : ℝ) (221802339531/500000000000 : ℝ) (44360467907/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 1 (598392555643/1000000000000 : ℝ) (299196277823/500000000000 : ℝ) (221802339531/500000000000 : ℝ) (44360467907/100000000000 : ℝ) (65124827169/125000000000 : ℝ) (260499308679/500000000000 : ℝ) (257609072821/500000000000 : ℝ) (515218145649/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 2 (65124827169/125000000000 : ℝ) (260499308679/500000000000 : ℝ) (257609072821/500000000000 : ℝ) (515218145649/1000000000000 : ℝ) (518108381497/1000000000000 : ℝ) (8095443461/15625000000 : ℝ) (129525079983/250000000000 : ℝ) (518100319939/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 3 (518108381497/1000000000000 : ℝ) (8095443461/15625000000 : ℝ) (129525079983/250000000000 : ℝ) (518100319939/1000000000000 : ℝ) (259052175357/500000000000 : ℝ) (259052175361/500000000000 : ℝ) (259052175349/500000000000 : ℝ) (259052175353/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 4 (259052175357/500000000000 : ℝ) (259052175361/500000000000 : ℝ) (259052175349/500000000000 : ℝ) (259052175353/500000000000 : ℝ) (259052175353/500000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 5 (259052175353/500000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 6 (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9059/65536 : ℝ))) 7 (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9059/65536 : ℝ)) hmem 8 (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9059/65536 : ℝ))) hcmem 8 (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9059/65536 : ℝ)) (495099594513/500000000000 : ℝ) (990199189029/1000000000000 : ℝ) (103620870141/200000000000 : ℝ) (259052175357/500000000000 : ℝ) (51368225959/62500000000 : ℝ) (410945807681/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0448_exp_lower
  have heNumeric : (50475732789/25000000000 : ℝ)/4 ≤ Real.exp (-5469420032271/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475732789/25000000000 : ℝ)/4 ≤ Real.exp ((4529/32768 : ℝ)-(410945807681/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4529/32768 : ℝ) (9059/65536 : ℝ) (410945807681/500000000000 : ℝ) (50475732789/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0449; no trusted numerical premise.
theorem cover7_leaf0449_exp_radius : (997534390533003501/1000000000000000000 : ℝ) ≤ Real.exp ((-2265/114688 : ℝ)/8) ∧ Real.exp ((-2265/114688 : ℝ)/8) ≤ (498767195266501751/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2265/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0449_exp_lower : (918090169462916481/1000000000000000000 : ℝ) ≤ Real.exp ((-10938837679293/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938837679293/16000000000000 : ℝ)/8) ≤ (459045084731458241/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938837679293/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0449_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019029612553/1000000000000 : ℝ) ≤ 4*Real.exp (9059/65536 : ℝ)*Real.exp (-mu (radius 7 (2265/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019029612553/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2265/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0449_exp_radius
  have hrNumeric : (490222252951/500000000000 : ℝ) ≤ Real.exp (-2265/114688 : ℝ) ∧ Real.exp (-2265/114688 : ℝ) ≤ (980444505903/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490222252951/500000000000 : ℝ) ≤ (radius 7 (2265/16384 : ℝ)) ∧ (radius 7 (2265/16384 : ℝ)) ≤ (980444505903/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2265/16384 : ℝ)) (490222252951/500000000000 : ℝ) (980444505903/1000000000000 : ℝ) (98397879607/500000000000 : ℝ) (9839787961/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2265/16384 : ℝ)) (490222252951/500000000000 : ℝ) (980444505903/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490222252951/500000000000 : ℝ) (980444505903/1000000000000 : ℝ) (990222252951/1000000000000 : ℝ) (123777781619/125000000000 : ℝ) (123771747199/125000000000 : ℝ) (495086988797/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 1 (990222252951/1000000000000 : ℝ) (123777781619/125000000000 : ℝ) (123771747199/125000000000 : ℝ) (495086988797/500000000000 : ℝ) (990198115271/1000000000000 : ℝ) (990198115273/1000000000000 : ℝ) (990198114977/1000000000000 : ℝ) (990198114979/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 2 (990198115271/1000000000000 : ℝ) (990198115273/1000000000000 : ℝ) (990198114977/1000000000000 : ℝ) (990198114979/1000000000000 : ℝ) (247549528781/250000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 3 (247549528781/250000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 4 (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 5 (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 6 (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2265/16384 : ℝ)) 7 (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2265/16384 : ℝ))) (98397879607/500000000000 : ℝ) (9839787961/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98397879607/500000000000 : ℝ) (9839787961/50000000000 : ℝ) (598397879607/1000000000000 : ℝ) (59839787961/100000000000 : ℝ) (88723336099/200000000000 : ℝ) (443616680503/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 1 (598397879607/1000000000000 : ℝ) (59839787961/100000000000 : ℝ) (88723336099/200000000000 : ℝ) (443616680503/1000000000000 : ℝ) (521007280051/1000000000000 : ℝ) (521007280057/1000000000000 : ℝ) (515227407041/1000000000000 : ℝ) (64403425881/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 2 (521007280051/1000000000000 : ℝ) (521007280057/1000000000000 : ℝ) (515227407041/1000000000000 : ℝ) (64403425881/125000000000 : ℝ) (259058671773/500000000000 : ℝ) (518117343553/1000000000000 : ℝ) (51810928379/100000000000 : ℝ) (259054641899/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 3 (259058671773/500000000000 : ℝ) (518117343553/1000000000000 : ℝ) (51810928379/100000000000 : ℝ) (259054641899/500000000000 : ℝ) (129528328417/250000000000 : ℝ) (129528328419/250000000000 : ℝ) (129528328413/250000000000 : ℝ) (25905665683/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 4 (129528328417/250000000000 : ℝ) (129528328419/250000000000 : ℝ) (129528328413/250000000000 : ℝ) (25905665683/50000000000 : ℝ) (25905665683/50000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 5 (25905665683/50000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 6 (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2265/16384 : ℝ))) 7 (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2265/16384 : ℝ)) hmem 8 (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2265/16384 : ℝ))) hcmem 8 (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2265/16384 : ℝ)) (990198115123/1000000000000 : ℝ) (495099057563/500000000000 : ℝ) (518113313659/1000000000000 : ℝ) (129528328417/250000000000 : ℝ) (164381345011/200000000000 : ℝ) (821906725073/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0449_exp_lower
  have heNumeric : (2019029612553/1000000000000 : ℝ)/4 ≤ Real.exp (-10938837679293/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019029612553/1000000000000 : ℝ)/4 ≤ Real.exp ((9059/65536 : ℝ)-(821906725073/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9059/65536 : ℝ) (2265/16384 : ℝ) (821906725073/1000000000000 : ℝ) (2019029612553/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0425_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0425_certificate
#check SmaleRate.Proofs.cover7_leaf0426_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0426_certificate
#check SmaleRate.Proofs.cover7_leaf0427_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0427_certificate
#check SmaleRate.Proofs.cover7_leaf0428_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0428_certificate
#check SmaleRate.Proofs.cover7_leaf0429_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0429_certificate
#check SmaleRate.Proofs.cover7_leaf0430_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0430_certificate
#check SmaleRate.Proofs.cover7_leaf0431_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0431_certificate
#check SmaleRate.Proofs.cover7_leaf0432_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0432_certificate
#check SmaleRate.Proofs.cover7_leaf0433_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0433_certificate
#check SmaleRate.Proofs.cover7_leaf0434_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0434_certificate
#check SmaleRate.Proofs.cover7_leaf0435_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0435_certificate
#check SmaleRate.Proofs.cover7_leaf0436_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0436_certificate
#check SmaleRate.Proofs.cover7_leaf0437_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0437_certificate
#check SmaleRate.Proofs.cover7_leaf0438_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0438_certificate
#check SmaleRate.Proofs.cover7_leaf0439_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0439_certificate
#check SmaleRate.Proofs.cover7_leaf0440_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0440_certificate
#check SmaleRate.Proofs.cover7_leaf0441_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0441_certificate
#check SmaleRate.Proofs.cover7_leaf0442_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0442_certificate
#check SmaleRate.Proofs.cover7_leaf0443_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0443_certificate
#check SmaleRate.Proofs.cover7_leaf0444_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0444_certificate
#check SmaleRate.Proofs.cover7_leaf0445_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0445_certificate
#check SmaleRate.Proofs.cover7_leaf0446_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0446_certificate
#check SmaleRate.Proofs.cover7_leaf0447_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0447_certificate
#check SmaleRate.Proofs.cover7_leaf0448_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0448_certificate
#check SmaleRate.Proofs.cover7_leaf0449_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0449_certificate
