/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0375; no trusted numerical premise.
theorem cover7_leaf0375_exp_radius : (997554504420548073/1000000000000000000 : ℝ) ≤ Real.exp ((-4493/229376 : ℝ)/8) ∧ Real.exp ((-4493/229376 : ℝ)/8) ≤ (498777252210274037/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4493/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0375_exp_lower : (918089249841761467/1000000000000000000 : ℝ) ≤ Real.exp ((-10938965892807/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938965892807/16000000000000 : ℝ)/8) ≤ (229522312460440367/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938965892807/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0375_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506716719/500000000000 : ℝ) ≤ 4*Real.exp (8985/65536 : ℝ)*Real.exp (-mu (radius 7 (4493/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506716719/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4493/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0375_exp_radius
  have hrNumeric : (196120534283/200000000000 : ℝ) ≤ Real.exp (-4493/229376 : ℝ) ∧ Real.exp (-4493/229376 : ℝ) ≤ (122575333927/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196120534283/200000000000 : ℝ) ≤ (radius 7 (4493/32768 : ℝ)) ∧ (radius 7 (4493/32768 : ℝ)) ≤ (122575333927/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4493/32768 : ℝ)) (196120534283/200000000000 : ℝ) (122575333927/125000000000 : ℝ) (24500765553/125000000000 : ℝ) (19600612443/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4493/32768 : ℝ)) (196120534283/200000000000 : ℝ) (122575333927/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196120534283/200000000000 : ℝ) (122575333927/125000000000 : ℝ) (990301335707/1000000000000 : ℝ) (247575333927/250000000000 : ℝ) (247563460477/250000000000 : ℝ) (99025384191/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 1 (990301335707/1000000000000 : ℝ) (247575333927/250000000000 : ℝ) (247563460477/250000000000 : ℝ) (99025384191/100000000000 : ℝ) (990277588807/1000000000000 : ℝ) (990277588809/1000000000000 : ℝ) (495138794261/500000000000 : ℝ) (39611103541/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 2 (990277588807/1000000000000 : ℝ) (990277588809/1000000000000 : ℝ) (495138794261/500000000000 : ℝ) (39611103541/40000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 3 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 4 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 5 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 6 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4493/32768 : ℝ)) 7 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4493/32768 : ℝ))) (24500765553/125000000000 : ℝ) (19600612443/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24500765553/125000000000 : ℝ) (19600612443/100000000000 : ℝ) (149500765553/250000000000 : ℝ) (119600612443/200000000000 : ℝ) (442725789201/1000000000000 : ℝ) (442725789209/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 1 (149500765553/250000000000 : ℝ) (119600612443/200000000000 : ℝ) (442725789201/1000000000000 : ℝ) (442725789209/1000000000000 : ℝ) (260182212853/500000000000 : ℝ) (32522776607/62500000000 : ℝ) (514539967021/1000000000000 : ℝ) (128634991757/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 2 (260182212853/500000000000 : ℝ) (32522776607/62500000000 : ℝ) (514539967021/1000000000000 : ℝ) (128634991757/250000000000 : ℝ) (517452196363/1000000000000 : ℝ) (51745219637/100000000000 : ℝ) (517444001261/1000000000000 : ℝ) (517444001269/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 3 (517452196363/1000000000000 : ℝ) (51745219637/100000000000 : ℝ) (517444001261/1000000000000 : ℝ) (517444001269/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (25872404941/50000000000 : ℝ) (103489619759/200000000000 : ℝ) (129362024701/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 4 (129362024703/250000000000 : ℝ) (25872404941/50000000000 : ℝ) (103489619759/200000000000 : ℝ) (129362024701/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 5 (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 6 (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4493/32768 : ℝ))) 7 (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4493/32768 : ℝ)) hmem 8 (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4493/32768 : ℝ))) hcmem 8 (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4493/32768 : ℝ)) (123784698583/125000000000 : ℝ) (990277588667/1000000000000 : ℝ) (517448098803/1000000000000 : ℝ) (129362024703/250000000000 : ℝ) (820785588009/1000000000000 : ℝ) (820785588027/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0375_exp_lower
  have heNumeric : (1009506716719/500000000000 : ℝ)/4 ≤ Real.exp (-10938965892807/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506716719/500000000000 : ℝ)/4 ≤ Real.exp ((8985/65536 : ℝ)-(820785588027/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8985/65536 : ℝ) (4493/32768 : ℝ) (820785588027/1000000000000 : ℝ) (1009506716719/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0376; no trusted numerical premise.
theorem cover7_leaf0376_exp_radius : (997554232608553653/1000000000000000000 : ℝ) ≤ Real.exp ((-8987/458752 : ℝ)/8) ∧ Real.exp ((-8987/458752 : ℝ)/8) ≤ (498777116304276827/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8987/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0376_exp_lower : (229522314391442073/250000000000000000 : ℝ) ≤ Real.exp ((-5469482407963/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469482407963/8000000000000 : ℝ)/8) ≤ (918089257565768293/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469482407963/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0376_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188348083/62500000000 : ℝ) ≤ 4*Real.exp (4493/32768 : ℝ)*Real.exp (-mu (radius 7 (8987/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (126188348083/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8987/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0376_exp_radius
  have hrNumeric : (980600533873/1000000000000 : ℝ) ≤ Real.exp (-8987/458752 : ℝ) ∧ Real.exp (-8987/458752 : ℝ) ≤ (490300266937/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980600533873/1000000000000 : ℝ) ≤ (radius 7 (8987/65536 : ℝ)) ∧ (radius 7 (8987/65536 : ℝ)) ≤ (490300266937/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8987/65536 : ℝ)) (980600533873/1000000000000 : ℝ) (490300266937/500000000000 : ℝ) (196016818069/1000000000000 : ℝ) (7840672723/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8987/65536 : ℝ)) (980600533873/1000000000000 : ℝ) (490300266937/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980600533873/1000000000000 : ℝ) (490300266937/500000000000 : ℝ) (123787533367/125000000000 : ℝ) (990300266937/1000000000000 : ℝ) (495126381309/500000000000 : ℝ) (990252762619/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 1 (123787533367/125000000000 : ℝ) (990300266937/1000000000000 : ℝ) (495126381309/500000000000 : ℝ) (990252762619/1000000000000 : ℝ) (990276514777/1000000000000 : ℝ) (495138257389/500000000000 : ℝ) (247569128623/250000000000 : ℝ) (495138257247/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 2 (990276514777/1000000000000 : ℝ) (495138257389/500000000000 : ℝ) (247569128623/250000000000 : ℝ) (495138257247/500000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 3 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 4 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 5 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 6 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8987/65536 : ℝ)) 7 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8987/65536 : ℝ))) (196016818069/1000000000000 : ℝ) (7840672723/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196016818069/1000000000000 : ℝ) (7840672723/40000000000 : ℝ) (299004204517/500000000000 : ℝ) (299004204519/500000000000 : ℝ) (55342233261/125000000000 : ℝ) (27671116631/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 1 (299004204517/500000000000 : ℝ) (299004204519/500000000000 : ℝ) (55342233261/125000000000 : ℝ) (27671116631/62500000000 : ℝ) (520373137561/1000000000000 : ℝ) (520373137567/1000000000000 : ℝ) (257274642609/500000000000 : ℝ) (20581971409/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 2 (520373137561/1000000000000 : ℝ) (520373137567/1000000000000 : ℝ) (257274642609/500000000000 : ℝ) (20581971409/40000000000 : ℝ) (517461211389/1000000000000 : ℝ) (129365302849/250000000000 : ℝ) (64681627267/125000000000 : ℝ) (16170406817/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 3 (517461211389/1000000000000 : ℝ) (129365302849/250000000000 : ℝ) (64681627267/125000000000 : ℝ) (16170406817/31250000000 : ℝ) (258728557381/500000000000 : ℝ) (51745711477/100000000000 : ℝ) (258728557373/500000000000 : ℝ) (258728557377/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 4 (258728557381/500000000000 : ℝ) (51745711477/100000000000 : ℝ) (258728557373/500000000000 : ℝ) (258728557377/500000000000 : ℝ) (258728557377/500000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 5 (258728557377/500000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 6 (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8987/65536 : ℝ))) 7 (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8987/65536 : ℝ)) hmem 8 (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8987/65536 : ℝ))) hcmem 8 (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8987/65536 : ℝ)) (495138257317/500000000000 : ℝ) (247569128659/250000000000 : ℝ) (517457114753/1000000000000 : ℝ) (258728557381/500000000000 : ℝ) (410400389747/500000000000 : ℝ) (820800779511/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0376_exp_lower
  have heNumeric : (126188348083/62500000000 : ℝ)/4 ≤ Real.exp (-5469482407963/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188348083/62500000000 : ℝ)/4 ≤ Real.exp ((4493/32768 : ℝ)-(820800779511/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4493/32768 : ℝ) (8987/65536 : ℝ) (820800779511/1000000000000 : ℝ) (126188348083/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0377; no trusted numerical premise.
theorem cover7_leaf0377_exp_radius : (199510792159326659/200000000000000000 : ℝ) ≤ Real.exp ((-321/16384 : ℝ)/8) ∧ Real.exp ((-321/16384 : ℝ)/8) ≤ (62347122549789581/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-321/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0377_exp_lower : (918089265419455291/1000000000000000000 : ℝ) ≤ Real.exp ((-2187792744193/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187792744193/3200000000000 : ℝ)/8) ≤ (229522316354863823/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187792744193/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0377_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013707499/1000000000000 : ℝ) ≤ 4*Real.exp (8987/65536 : ℝ)*Real.exp (-mu (radius 7 (2247/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013707499/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2247/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0377_exp_radius
  have hrNumeric : (61287399771/62500000000 : ℝ) ≤ Real.exp (-321/16384 : ℝ) ∧ Real.exp (-321/16384 : ℝ) ≤ (980598396337/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61287399771/62500000000 : ℝ) ≤ (radius 7 (2247/16384 : ℝ)) ∧ (radius 7 (2247/16384 : ℝ)) ≤ (980598396337/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2247/16384 : ℝ)) (61287399771/62500000000 : ℝ) (980598396337/1000000000000 : ℝ) (98013755541/500000000000 : ℝ) (12251719443/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2247/16384 : ℝ)) (61287399771/62500000000 : ℝ) (980598396337/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61287399771/62500000000 : ℝ) (980598396337/1000000000000 : ℝ) (123787399771/125000000000 : ℝ) (990299198169/1000000000000 : ℝ) (990251683329/1000000000000 : ℝ) (99025168333/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 1 (123787399771/125000000000 : ℝ) (990299198169/1000000000000 : ℝ) (990251683329/1000000000000 : ℝ) (99025168333/100000000000 : ℝ) (247568860187/250000000000 : ℝ) (3961101763/4000000000 : ℝ) (990275440463/1000000000000 : ℝ) (198055088093/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 2 (247568860187/250000000000 : ℝ) (3961101763/4000000000 : ℝ) (990275440463/1000000000000 : ℝ) (198055088093/200000000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 3 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 4 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 5 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 6 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2247/16384 : ℝ)) 7 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2247/16384 : ℝ))) (98013755541/500000000000 : ℝ) (12251719443/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98013755541/500000000000 : ℝ) (12251719443/62500000000 : ℝ) (598013755541/1000000000000 : ℝ) (74751719443/125000000000 : ℝ) (442749941933/1000000000000 : ℝ) (442749941941/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 1 (598013755541/1000000000000 : ℝ) (74751719443/125000000000 : ℝ) (442749941933/1000000000000 : ℝ) (442749941941/1000000000000 : ℝ) (520381848737/1000000000000 : ℝ) (520381848743/1000000000000 : ℝ) (51455860263/100000000000 : ℝ) (514558602637/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 2 (520381848737/1000000000000 : ℝ) (520381848743/1000000000000 : ℝ) (51455860263/100000000000 : ℝ) (514558602637/1000000000000 : ℝ) (517470225683/1000000000000 : ℝ) (51747022569/100000000000 : ℝ) (258731017139/500000000000 : ℝ) (258731017143/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 3 (517470225683/1000000000000 : ℝ) (51747022569/100000000000 : ℝ) (258731017139/500000000000 : ℝ) (258731017143/500000000000 : ℝ) (25873306499/50000000000 : ℝ) (129366532497/250000000000 : ℝ) (129366532491/250000000000 : ℝ) (129366532493/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 4 (25873306499/50000000000 : ℝ) (129366532497/250000000000 : ℝ) (129366532491/250000000000 : ℝ) (129366532493/250000000000 : ℝ) (129366532493/250000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 5 (129366532493/250000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 6 (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2247/16384 : ℝ))) 7 (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2247/16384 : ℝ)) hmem 8 (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2247/16384 : ℝ))) hcmem 8 (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2247/16384 : ℝ)) (198055088121/200000000000 : ℝ) (30946107519/31250000000 : ℝ) (517466129971/1000000000000 : ℝ) (25873306499/50000000000 : ℝ) (820815969847/1000000000000 : ℝ) (164163193973/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0377_exp_lower
  have heNumeric : (2019013707499/1000000000000 : ℝ)/4 ≤ Real.exp (-2187792744193/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013707499/1000000000000 : ℝ)/4 ≤ Real.exp ((8987/65536 : ℝ)-(164163193973/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8987/65536 : ℝ) (2247/16384 : ℝ) (164163193973/200000000000 : ℝ) (2019013707499/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0378; no trusted numerical premise.
theorem cover7_leaf0378_exp_radius : (997553688984787001/1000000000000000000 : ℝ) ≤ Real.exp ((-8989/458752 : ℝ)/8) ∧ Real.exp ((-8989/458752 : ℝ)/8) ≤ (498776844492393501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8989/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0378_exp_lower : (459044636701353853/500000000000000000 : ℝ) ≤ Real.exp ((-546948130397/800000000000 : ℝ)/8) ∧ Real.exp ((-546948130397/800000000000 : ℝ)/8) ≤ (918089273402707707/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546948130397/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0378_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (40380276959/20000000000 : ℝ) ≤ 4*Real.exp (2247/16384 : ℝ)*Real.exp (-mu (radius 7 (8989/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (40380276959/20000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8989/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0378_exp_radius
  have hrNumeric : (245149064701/250000000000 : ℝ) ≤ Real.exp (-8989/458752 : ℝ) ∧ Real.exp (-8989/458752 : ℝ) ≤ (196119251761/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245149064701/250000000000 : ℝ) ≤ (radius 7 (8989/65536 : ℝ)) ∧ (radius 7 (8989/65536 : ℝ)) ≤ (196119251761/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8989/65536 : ℝ)) (245149064701/250000000000 : ℝ) (196119251761/200000000000 : ℝ) (24504775433/125000000000 : ℝ) (19603820347/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8989/65536 : ℝ)) (245149064701/250000000000 : ℝ) (196119251761/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245149064701/250000000000 : ℝ) (196119251761/200000000000 : ℝ) (495149064701/500000000000 : ℝ) (990298129403/1000000000000 : ℝ) (990250604041/1000000000000 : ℝ) (495125302021/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 1 (495149064701/500000000000 : ℝ) (990298129403/1000000000000 : ℝ) (990250604041/1000000000000 : ℝ) (495125302021/500000000000 : ℝ) (990274366721/1000000000000 : ℝ) (990274366723/1000000000000 : ℝ) (247568591609/250000000000 : ℝ) (495137183219/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 2 (990274366721/1000000000000 : ℝ) (990274366723/1000000000000 : ℝ) (247568591609/250000000000 : ℝ) (495137183219/500000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 3 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 4 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 5 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 6 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8989/65536 : ℝ)) 7 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8989/65536 : ℝ))) (24504775433/125000000000 : ℝ) (19603820347/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24504775433/125000000000 : ℝ) (19603820347/100000000000 : ℝ) (149504775433/250000000000 : ℝ) (119603820347/200000000000 : ℝ) (88552403347/200000000000 : ℝ) (442762016743/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 1 (149504775433/250000000000 : ℝ) (119603820347/200000000000 : ℝ) (88552403347/200000000000 : ℝ) (442762016743/1000000000000 : ℝ) (520390559233/1000000000000 : ℝ) (520390559239/1000000000000 : ℝ) (514567919257/1000000000000 : ℝ) (16080247477/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 2 (520390559233/1000000000000 : ℝ) (520390559239/1000000000000 : ℝ) (514567919257/1000000000000 : ℝ) (16080247477/31250000000 : ℝ) (103495847849/200000000000 : ℝ) (129369809813/250000000000 : ℝ) (64683881211/125000000000 : ℝ) (103494209939/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 3 (103495847849/200000000000 : ℝ) (129369809813/250000000000 : ℝ) (64683881211/125000000000 : ℝ) (103494209939/200000000000 : ℝ) (258737572233/500000000000 : ℝ) (258737572237/500000000000 : ℝ) (10349502889/20000000000 : ℝ) (258737572229/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 4 (258737572233/500000000000 : ℝ) (258737572237/500000000000 : ℝ) (10349502889/20000000000 : ℝ) (258737572229/500000000000 : ℝ) (258737572229/500000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 5 (258737572229/500000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 6 (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8989/65536 : ℝ))) 7 (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8989/65536 : ℝ)) hmem 8 (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8989/65536 : ℝ))) hcmem 8 (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8989/65536 : ℝ)) (495137183289/500000000000 : ℝ) (990274366581/1000000000000 : ℝ) (517475144457/1000000000000 : ℝ) (258737572233/500000000000 : ℝ) (25650973721/31250000000 : ℝ) (82083115909/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0378_exp_lower
  have heNumeric : (40380276959/20000000000 : ℝ)/4 ≤ Real.exp (-546948130397/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (40380276959/20000000000 : ℝ)/4 ≤ Real.exp ((2247/16384 : ℝ)-(82083115909/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2247/16384 : ℝ) (8989/65536 : ℝ) (82083115909/100000000000 : ℝ) (40380276959/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0379; no trusted numerical premise.
theorem cover7_leaf0379_exp_radius : (997553417173014769/1000000000000000000 : ℝ) ≤ Real.exp ((-4495/229376 : ℝ)/8) ∧ Real.exp ((-4495/229376 : ℝ)/8) ≤ (99755341717301477/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4495/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0379_exp_lower : (918089281514836973/1000000000000000000 : ℝ) ≤ Real.exp ((-10938961476947/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938961476947/16000000000000 : ℝ)/8) ≤ (459044640757418487/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938961476947/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0379_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753497667/250000000000 : ℝ) ≤ 4*Real.exp (8989/65536 : ℝ)*Real.exp (-mu (radius 7 (4495/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504753497667/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4495/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0379_exp_radius
  have hrNumeric : (245148530319/250000000000 : ℝ) ≤ Real.exp (-4495/229376 : ℝ) ∧ Real.exp (-4495/229376 : ℝ) ≤ (980594121277/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245148530319/250000000000 : ℝ) ≤ (radius 7 (4495/32768 : ℝ)) ∧ (radius 7 (4495/32768 : ℝ)) ≤ (980594121277/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4495/32768 : ℝ)) (245148530319/250000000000 : ℝ) (980594121277/1000000000000 : ℝ) (9802444761/50000000000 : ℝ) (98024447613/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4495/32768 : ℝ)) (245148530319/250000000000 : ℝ) (980594121277/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245148530319/250000000000 : ℝ) (980594121277/1000000000000 : ℝ) (495148530319/500000000000 : ℝ) (990297060639/1000000000000 : ℝ) (495124762377/500000000000 : ℝ) (198049904951/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 1 (495148530319/500000000000 : ℝ) (990297060639/1000000000000 : ℝ) (495124762377/500000000000 : ℝ) (198049904951/200000000000 : ℝ) (123784161587/125000000000 : ℝ) (990273292697/1000000000000 : ℝ) (99027329241/100000000000 : ℝ) (247568323103/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 2 (123784161587/125000000000 : ℝ) (990273292697/1000000000000 : ℝ) (99027329241/100000000000 : ℝ) (247568323103/250000000000 : ℝ) (990273292553/1000000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 3 (990273292553/1000000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 4 (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 5 (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 6 (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4495/32768 : ℝ)) 7 (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4495/32768 : ℝ))) (9802444761/50000000000 : ℝ) (98024447613/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9802444761/50000000000 : ℝ) (98024447613/500000000000 : ℝ) (59802444761/100000000000 : ℝ) (598024447613/1000000000000 : ℝ) (221387045251/500000000000 : ℝ) (442774090509/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 1 (59802444761/100000000000 : ℝ) (598024447613/1000000000000 : ℝ) (221387045251/500000000000 : ℝ) (442774090509/1000000000000 : ℝ) (8131238579/15625000000 : ℝ) (520399269061/1000000000000 : ℝ) (102915447021/200000000000 : ℝ) (514577235111/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 2 (8131238579/15625000000 : ℝ) (520399269061/1000000000000 : ℝ) (102915447021/200000000000 : ℝ) (514577235111/1000000000000 : ℝ) (6468603151/12500000000 : ℝ) (258744126043/500000000000 : ℝ) (517480064371/1000000000000 : ℝ) (517480064377/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 3 (6468603151/12500000000 : ℝ) (258744126043/500000000000 : ℝ) (517480064371/1000000000000 : ℝ) (517480064377/1000000000000 : ℝ) (20699366329/40000000000 : ℝ) (64685519779/125000000000 : ℝ) (517484158209/1000000000000 : ℝ) (64685519777/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 4 (20699366329/40000000000 : ℝ) (64685519779/125000000000 : ℝ) (517484158209/1000000000000 : ℝ) (64685519777/125000000000 : ℝ) (517484158217/1000000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 5 (517484158217/1000000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 6 (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4495/32768 : ℝ))) 7 (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4495/32768 : ℝ)) hmem 8 (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4495/32768 : ℝ))) hcmem 8 (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4495/32768 : ℝ)) (123784161569/125000000000 : ℝ) (198054658511/200000000000 : ℝ) (64685519777/125000000000 : ℝ) (32342759889/62500000000 : ℝ) (102605793397/125000000000 : ℝ) (102605793399/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0379_exp_lower
  have heNumeric : (504753497667/250000000000 : ℝ)/4 ≤ Real.exp (-10938961476947/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753497667/250000000000 : ℝ)/4 ≤ Real.exp ((8989/65536 : ℝ)-(102605793399/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8989/65536 : ℝ) (4495/32768 : ℝ) (102605793399/125000000000 : ℝ) (504753497667/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0380; no trusted numerical premise.
theorem cover7_leaf0380_exp_radius : (4987765726806583/5000000000000000 : ℝ) ≤ Real.exp ((-8991/458752 : ℝ)/8) ∧ Real.exp ((-8991/458752 : ℝ)/8) ≤ (997553145361316601/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8991/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0380_exp_lower : (459044644878265831/500000000000000000 : ℝ) ≤ Real.exp ((-1093896032789/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093896032789/1600000000000 : ℝ)/8) ≤ (918089289756531663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093896032789/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0380_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009507067833/500000000000 : ℝ) ≤ 4*Real.exp (4495/32768 : ℝ)*Real.exp (-mu (radius 7 (8991/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009507067833/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8991/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0380_exp_radius
  have hrNumeric : (980591983753/1000000000000 : ℝ) ≤ Real.exp (-8991/458752 : ℝ) ∧ Real.exp (-8991/458752 : ℝ) ≤ (490295991877/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980591983753/1000000000000 : ℝ) ≤ (radius 7 (8991/65536 : ℝ)) ∧ (radius 7 (8991/65536 : ℝ)) ≤ (490295991877/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8991/65536 : ℝ)) (980591983753/1000000000000 : ℝ) (490295991877/500000000000 : ℝ) (24507448293/125000000000 : ℝ) (3921191727/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8991/65536 : ℝ)) (980591983753/1000000000000 : ℝ) (490295991877/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980591983753/1000000000000 : ℝ) (490295991877/500000000000 : ℝ) (247573997969/250000000000 : ℝ) (990295991877/1000000000000 : ℝ) (247562111367/250000000000 : ℝ) (99024844547/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 1 (247573997969/250000000000 : ℝ) (990295991877/1000000000000 : ℝ) (247562111367/250000000000 : ℝ) (99024844547/100000000000 : ℝ) (61892013667/62500000000 : ℝ) (495136109337/500000000000 : ℝ) (495136109193/500000000000 : ℝ) (990272218389/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 2 (61892013667/62500000000 : ℝ) (495136109337/500000000000 : ℝ) (495136109193/500000000000 : ℝ) (990272218389/1000000000000 : ℝ) (990272218529/1000000000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 3 (990272218529/1000000000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 4 (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 5 (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 6 (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8991/65536 : ℝ)) 7 (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8991/65536 : ℝ))) (24507448293/125000000000 : ℝ) (3921191727/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24507448293/125000000000 : ℝ) (3921191727/20000000000 : ℝ) (149507448293/250000000000 : ℝ) (23921191727/40000000000 : ℝ) (17711446529/40000000000 : ℝ) (442786163233/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 1 (149507448293/250000000000 : ℝ) (23921191727/40000000000 : ℝ) (17711446529/40000000000 : ℝ) (442786163233/1000000000000 : ℝ) (260203989099/500000000000 : ℝ) (130101994551/250000000000 : ℝ) (514586550167/1000000000000 : ℝ) (257293275087/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 2 (260203989099/500000000000 : ℝ) (130101994551/250000000000 : ℝ) (514586550167/1000000000000 : ℝ) (257293275087/500000000000 : ℝ) (258748632091/500000000000 : ℝ) (517497264189/1000000000000 : ℝ) (517489078319/1000000000000 : ℝ) (517489078327/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 3 (258748632091/500000000000 : ℝ) (517497264189/1000000000000 : ℝ) (517489078319/1000000000000 : ℝ) (517489078327/1000000000000 : ℝ) (413994537/800000000 : ℝ) (258746585629/500000000000 : ℝ) (258746585617/500000000000 : ℝ) (258746585621/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 4 (413994537/800000000 : ℝ) (258746585629/500000000000 : ℝ) (258746585617/500000000000 : ℝ) (258746585621/500000000000 : ℝ) (258746585621/500000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 5 (258746585621/500000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 6 (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8991/65536 : ℝ))) 7 (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8991/65536 : ℝ)) hmem 8 (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8991/65536 : ℝ))) hcmem 8 (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8991/65536 : ℝ)) (30946006829/31250000000 : ℝ) (247568054633/250000000000 : ℝ) (517493171241/1000000000000 : ℝ) (413994537/800000000 : ℝ) (410430767073/500000000000 : ℝ) (164172306833/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0380_exp_lower
  have heNumeric : (1009507067833/500000000000 : ℝ)/4 ≤ Real.exp (-1093896032789/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009507067833/500000000000 : ℝ)/4 ≤ Real.exp ((4495/32768 : ℝ)-(164172306833/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4495/32768 : ℝ) (8991/65536 : ℝ) (164172306833/200000000000 : ℝ) (1009507067833/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0381; no trusted numerical premise.
theorem cover7_leaf0381_exp_radius : (498776436774846247/500000000000000000 : ℝ) ≤ Real.exp ((-281/14336 : ℝ)/8) ∧ Real.exp ((-281/14336 : ℝ)/8) ≤ (199510574709938499/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-281/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0381_exp_lower : (459044649063666367/500000000000000000 : ℝ) ≤ Real.exp ((-10938959160833/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938959160833/16000000000000 : ℝ)/8) ≤ (183617859625466547/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938959160833/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0381_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802856587/200000000000 : ℝ) ≤ 4*Real.exp (8991/65536 : ℝ)*Real.exp (-mu (radius 7 (281/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403802856587/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (281/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0381_exp_radius
  have hrNumeric : (490294923117/500000000000 : ℝ) ≤ Real.exp (-281/14336 : ℝ) ∧ Real.exp (-281/14336 : ℝ) ≤ (196117969247/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490294923117/500000000000 : ℝ) ≤ (radius 7 (281/2048 : ℝ)) ∧ (radius 7 (281/2048 : ℝ)) ≤ (196117969247/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (281/2048 : ℝ)) (490294923117/500000000000 : ℝ) (196117969247/200000000000 : ℝ) (196070276841/1000000000000 : ℝ) (196070276847/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (281/2048 : ℝ)) (490294923117/500000000000 : ℝ) (196117969247/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (281/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490294923117/500000000000 : ℝ) (196117969247/200000000000 : ℝ) (990294923117/1000000000000 : ℝ) (495147461559/500000000000 : ℝ) (990247366183/1000000000000 : ℝ) (198049473237/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (281/2048 : ℝ)) 1 (990294923117/1000000000000 : ℝ) (495147461559/500000000000 : ℝ) (990247366183/1000000000000 : ℝ) (198049473237/200000000000 : ℝ) (19805422893/20000000000 : ℝ) (247567786163/250000000000 : ℝ) (247567786091/250000000000 : ℝ) (990271144367/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (281/2048 : ℝ)) 2 (19805422893/20000000000 : ℝ) (247567786163/250000000000 : ℝ) (247567786091/250000000000 : ℝ) (990271144367/1000000000000 : ℝ) (990271144507/1000000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (281/2048 : ℝ)) 3 (990271144507/1000000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (281/2048 : ℝ)) 4 (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (281/2048 : ℝ)) 5 (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (281/2048 : ℝ)) 6 (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (281/2048 : ℝ)) 7 (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (281/2048 : ℝ))) (196070276841/1000000000000 : ℝ) (196070276847/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196070276841/1000000000000 : ℝ) (196070276847/1000000000000 : ℝ) (29901756921/50000000000 : ℝ) (74754392303/125000000000 : ℝ) (442798234911/1000000000000 : ℝ) (442798234919/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 1 (29901756921/50000000000 : ℝ) (74754392303/125000000000 : ℝ) (442798234911/1000000000000 : ℝ) (442798234919/1000000000000 : ℝ) (104083337333/200000000000 : ℝ) (32526042917/62500000000 : ℝ) (4020280191/7812500000 : ℝ) (102919172891/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 2 (104083337333/200000000000 : ℝ) (32526042917/62500000000 : ℝ) (4020280191/7812500000 : ℝ) (102919172891/200000000000 : ℝ) (129376568889/250000000000 : ℝ) (129376568891/250000000000 : ℝ) (517498091539/1000000000000 : ℝ) (517498091547/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 3 (129376568889/250000000000 : ℝ) (129376568891/250000000000 : ℝ) (517498091539/1000000000000 : ℝ) (517498091547/1000000000000 : ℝ) (517502183547/1000000000000 : ℝ) (129375545889/250000000000 : ℝ) (517502183531/1000000000000 : ℝ) (25875109177/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 4 (517502183547/1000000000000 : ℝ) (129375545889/250000000000 : ℝ) (517502183531/1000000000000 : ℝ) (25875109177/50000000000 : ℝ) (517502183539/1000000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 5 (517502183539/1000000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 6 (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (281/2048 : ℝ))) 7 (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (281/2048 : ℝ)) hmem 8 (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (281/2048 : ℝ))) hcmem 8 (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (281/2048 : ℝ)) (495135572253/500000000000 : ℝ) (99027114451/100000000000 : ℝ) (258751091769/500000000000 : ℝ) (129375545887/250000000000 : ℝ) (820876719993/1000000000000 : ℝ) (820876720013/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0381_exp_lower
  have heNumeric : (403802856587/200000000000 : ℝ)/4 ≤ Real.exp (-10938959160833/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802856587/200000000000 : ℝ)/4 ≤ Real.exp ((8991/65536 : ℝ)-(820876720013/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8991/65536 : ℝ) (281/2048 : ℝ) (820876720013/1000000000000 : ℝ) (403802856587/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0382; no trusted numerical premise.
theorem cover7_leaf0382_exp_radius : (997552601738142451/1000000000000000000 : ℝ) ≤ Real.exp ((-8993/458752 : ℝ)/8) ∧ Real.exp ((-8993/458752 : ℝ)/8) ≤ (249388150434535613/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8993/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0382_exp_lower : (183617861325539847/200000000000000000 : ℝ) ≤ Real.exp ((-341842436741/500000000000 : ℝ)/8) ∧ Real.exp ((-341842436741/500000000000 : ℝ)/8) ≤ (229522326656924809/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341842436741/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0382_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014432483/1000000000000 : ℝ) ≤ 4*Real.exp (281/2048 : ℝ)*Real.exp (-mu (radius 7 (8993/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014432483/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8993/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0382_exp_radius
  have hrNumeric : (12257346359/12500000000 : ℝ) ≤ Real.exp (-8993/458752 : ℝ) ∧ Real.exp (-8993/458752 : ℝ) ≤ (980587708721/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12257346359/12500000000 : ℝ) ≤ (radius 7 (8993/65536 : ℝ)) ∧ (radius 7 (8993/65536 : ℝ)) ≤ (980587708721/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8993/65536 : ℝ)) (12257346359/12500000000 : ℝ) (980587708721/1000000000000 : ℝ) (49020241677/250000000000 : ℝ) (98040483357/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8993/65536 : ℝ)) (12257346359/12500000000 : ℝ) (980587708721/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12257346359/12500000000 : ℝ) (980587708721/1000000000000 : ℝ) (24757346359/25000000000 : ℝ) (990293854361/1000000000000 : ℝ) (9902462869/10000000000 : ℝ) (990246286901/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 1 (24757346359/25000000000 : ℝ) (990293854361/1000000000000 : ℝ) (9902462869/10000000000 : ℝ) (990246286901/1000000000000 : ℝ) (99027007063/100000000000 : ℝ) (990270070631/1000000000000 : ℝ) (123783758793/125000000000 : ℝ) (495135035173/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 2 (99027007063/100000000000 : ℝ) (990270070631/1000000000000 : ℝ) (123783758793/125000000000 : ℝ) (495135035173/500000000000 : ℝ) (990270070487/1000000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 3 (990270070487/1000000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 4 (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 5 (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 6 (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8993/65536 : ℝ)) 7 (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8993/65536 : ℝ))) (49020241677/250000000000 : ℝ) (98040483357/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49020241677/250000000000 : ℝ) (98040483357/500000000000 : ℝ) (299020241677/500000000000 : ℝ) (598040483357/1000000000000 : ℝ) (442810305557/1000000000000 : ℝ) (88562061113/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 1 (299020241677/500000000000 : ℝ) (598040483357/1000000000000 : ℝ) (442810305557/1000000000000 : ℝ) (88562061113/200000000000 : ℝ) (104085078891/200000000000 : ℝ) (520425394461/1000000000000 : ℝ) (257302588973/500000000000 : ℝ) (514605177953/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 2 (104085078891/200000000000 : ℝ) (520425394461/1000000000000 : ℝ) (257302588973/500000000000 : ℝ) (514605177953/1000000000000 : ℝ) (2587576431/5000000000 : ℝ) (517515286207/1000000000000 : ℝ) (517507104029/1000000000000 : ℝ) (517507104037/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 3 (2587576431/5000000000 : ℝ) (517515286207/1000000000000 : ℝ) (517507104029/1000000000000 : ℝ) (517507104037/1000000000000 : ℝ) (258755597557/500000000000 : ℝ) (258755597561/500000000000 : ℝ) (258755597549/500000000000 : ℝ) (258755597553/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 4 (258755597557/500000000000 : ℝ) (258755597561/500000000000 : ℝ) (258755597549/500000000000 : ℝ) (258755597553/500000000000 : ℝ) (258755597553/500000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 5 (258755597553/500000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 6 (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8993/65536 : ℝ))) 7 (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8993/65536 : ℝ)) hmem 8 (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8993/65536 : ℝ))) hcmem 8 (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8993/65536 : ℝ)) (495135035243/500000000000 : ℝ) (990270070489/1000000000000 : ℝ) (103502239021/200000000000 : ℝ) (258755597557/500000000000 : ℝ) (164178380943/200000000000 : ℝ) (205222976183/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0382_exp_lower
  have heNumeric : (2019014432483/1000000000000 : ℝ)/4 ≤ Real.exp (-341842436741/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014432483/1000000000000 : ℝ)/4 ≤ Real.exp ((281/2048 : ℝ)-(205222976183/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (281/2048 : ℝ) (8993/65536 : ℝ) (205222976183/250000000000 : ℝ) (2019014432483/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0383; no trusted numerical premise.
theorem cover7_leaf0383_exp_radius : (99755232992666647/100000000000000000 : ℝ) ≤ Real.exp ((-4497/229376 : ℝ)/8) ∧ Real.exp ((-4497/229376 : ℝ)/8) ≤ (997552329926666471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4497/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0383_exp_lower : (918089315257401647/1000000000000000000 : ℝ) ≤ Real.exp ((-10938956772559/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938956772559/16000000000000 : ℝ)/8) ≤ (57380582203587603/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938956772559/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0383_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014584307/1000000000000 : ℝ) ≤ 4*Real.exp (8993/65536 : ℝ)*Real.exp (-mu (radius 7 (4497/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014584307/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4497/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0383_exp_radius
  have hrNumeric : (980585571211/1000000000000 : ℝ) ≤ Real.exp (-4497/229376 : ℝ) ∧ Real.exp (-4497/229376 : ℝ) ≤ (245146392803/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980585571211/1000000000000 : ℝ) ≤ (radius 7 (4497/32768 : ℝ)) ∧ (radius 7 (4497/32768 : ℝ)) ≤ (245146392803/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4497/32768 : ℝ)) (980585571211/1000000000000 : ℝ) (245146392803/250000000000 : ℝ) (196091655943/1000000000000 : ℝ) (196091655949/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4497/32768 : ℝ)) (980585571211/1000000000000 : ℝ) (245146392803/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980585571211/1000000000000 : ℝ) (245146392803/250000000000 : ℝ) (198058557121/200000000000 : ℝ) (495146392803/500000000000 : ℝ) (495122603809/500000000000 : ℝ) (990245207619/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 1 (198058557121/200000000000 : ℝ) (495146392803/500000000000 : ℝ) (495122603809/500000000000 : ℝ) (990245207619/1000000000000 : ℝ) (990268996611/1000000000000 : ℝ) (990268996613/1000000000000 : ℝ) (39610759853/40000000000 : ℝ) (990268996327/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 2 (990268996611/1000000000000 : ℝ) (990268996613/1000000000000 : ℝ) (39610759853/40000000000 : ℝ) (990268996327/1000000000000 : ℝ) (247567249117/250000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 3 (247567249117/250000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 4 (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 5 (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 6 (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4497/32768 : ℝ)) 7 (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4497/32768 : ℝ))) (196091655943/1000000000000 : ℝ) (196091655949/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196091655943/1000000000000 : ℝ) (196091655949/1000000000000 : ℝ) (598045827971/1000000000000 : ℝ) (23921833119/40000000000 : ℝ) (11070559379/25000000000 : ℝ) (1729774903/3906250000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 1 (598045827971/1000000000000 : ℝ) (23921833119/40000000000 : ℝ) (11070559379/25000000000 : ℝ) (1729774903/3906250000 : ℝ) (104086820313/200000000000 : ℝ) (130108525393/250000000000 : ℝ) (514614490659/1000000000000 : ℝ) (257307245333/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 2 (104086820313/200000000000 : ℝ) (130108525393/250000000000 : ℝ) (514614490659/1000000000000 : ℝ) (257307245333/500000000000 : ℝ) (32345268507/62500000000 : ℝ) (517524296119/1000000000000 : ℝ) (258758057893/500000000000 : ℝ) (258758057897/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 3 (32345268507/62500000000 : ℝ) (517524296119/1000000000000 : ℝ) (258758057893/500000000000 : ℝ) (258758057897/500000000000 : ℝ) (517520205949/1000000000000 : ℝ) (517520205957/1000000000000 : ℝ) (129380051483/250000000000 : ℝ) (517520205941/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 4 (517520205949/1000000000000 : ℝ) (517520205957/1000000000000 : ℝ) (129380051483/250000000000 : ℝ) (517520205941/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 5 (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 6 (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4497/32768 : ℝ))) 7 (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4497/32768 : ℝ)) hmem 8 (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4497/32768 : ℝ))) hcmem 8 (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4497/32768 : ℝ)) (990268996467/1000000000000 : ℝ) (99026899647/100000000000 : ℝ) (25876010297/50000000000 : ℝ) (517520205949/1000000000000 : ℝ) (410453544153/500000000000 : ℝ) (205226772081/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0383_exp_lower
  have heNumeric : (2019014584307/1000000000000 : ℝ)/4 ≤ Real.exp (-10938956772559/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014584307/1000000000000 : ℝ)/4 ≤ Real.exp ((8993/65536 : ℝ)-(205226772081/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8993/65536 : ℝ) (4497/32768 : ℝ) (205226772081/250000000000 : ℝ) (2019014584307/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0384; no trusted numerical premise.
theorem cover7_leaf0384_exp_radius : (124694007264408069/125000000000000000 : ℝ) ≤ Real.exp ((-1285/65536 : ℝ)/8) ∧ Real.exp ((-1285/65536 : ℝ)/8) ≤ (997552058115264553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1285/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0384_exp_lower : (7172572843874851/7812500000000000 : ℝ) ≤ Real.exp ((-5469477775719/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469477775719/8000000000000 : ℝ)/8) ≤ (918089324015980929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469477775719/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0384_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014738399/1000000000000 : ℝ) ≤ 4*Real.exp (4497/32768 : ℝ)*Real.exp (-mu (radius 7 (8995/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014738399/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8995/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0384_exp_radius
  have hrNumeric : (490291716853/500000000000 : ℝ) ≤ Real.exp (-1285/65536 : ℝ) ∧ Real.exp (-1285/65536 : ℝ) ≤ (980583433707/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490291716853/500000000000 : ℝ) ≤ (radius 7 (8995/65536 : ℝ)) ∧ (radius 7 (8995/65536 : ℝ)) ≤ (980583433707/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8995/65536 : ℝ)) (490291716853/500000000000 : ℝ) (980583433707/1000000000000 : ℝ) (196102344553/1000000000000 : ℝ) (196102344559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8995/65536 : ℝ)) (490291716853/500000000000 : ℝ) (980583433707/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490291716853/500000000000 : ℝ) (980583433707/1000000000000 : ℝ) (990291716853/1000000000000 : ℝ) (495145858427/500000000000 : ℝ) (990244128337/1000000000000 : ℝ) (495122064169/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 1 (990291716853/1000000000000 : ℝ) (495145858427/500000000000 : ℝ) (990244128337/1000000000000 : ℝ) (495122064169/500000000000 : ℝ) (198053584519/200000000000 : ℝ) (247566980649/250000000000 : ℝ) (990267922309/1000000000000 : ℝ) (990267922311/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 2 (198053584519/200000000000 : ℝ) (247566980649/250000000000 : ℝ) (990267922309/1000000000000 : ℝ) (990267922311/1000000000000 : ℝ) (247566980613/250000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 3 (247566980613/250000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 4 (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 5 (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 6 (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8995/65536 : ℝ)) 7 (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8995/65536 : ℝ))) (196102344553/1000000000000 : ℝ) (196102344559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196102344553/1000000000000 : ℝ) (196102344559/1000000000000 : ℝ) (149512793069/250000000000 : ℝ) (14951279307/25000000000 : ℝ) (442834443729/1000000000000 : ℝ) (442834443737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 1 (149512793069/250000000000 : ℝ) (14951279307/25000000000 : ℝ) (442834443729/1000000000000 : ℝ) (442834443737/1000000000000 : ℝ) (260221404001/500000000000 : ℝ) (520442808009/1000000000000 : ℝ) (257311901297/500000000000 : ℝ) (514623802601/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 2 (260221404001/500000000000 : ℝ) (520442808009/1000000000000 : ℝ) (257311901297/500000000000 : ℝ) (514623802601/1000000000000 : ℝ) (258766652649/500000000000 : ℝ) (103506661061/200000000000 : ℝ) (16172660213/31250000000 : ℝ) (64690640853/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 3 (258766652649/500000000000 : ℝ) (103506661061/200000000000 : ℝ) (16172660213/31250000000 : ℝ) (64690640853/125000000000 : ℝ) (517529216057/1000000000000 : ℝ) (103505843213/200000000000 : ℝ) (12938230401/25000000000 : ℝ) (517529216049/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 4 (517529216057/1000000000000 : ℝ) (103505843213/200000000000 : ℝ) (12938230401/25000000000 : ℝ) (517529216049/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 5 (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 6 (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8995/65536 : ℝ))) 7 (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8995/65536 : ℝ)) hmem 8 (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8995/65536 : ℝ))) hcmem 8 (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8995/65536 : ℝ)) (990267922451/1000000000000 : ℝ) (495133961227/500000000000 : ℝ) (32345576003/62500000000 : ℝ) (517529216057/1000000000000 : ℝ) (32836890831/40000000000 : ℝ) (820922270793/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0384_exp_lower
  have heNumeric : (2019014738399/1000000000000 : ℝ)/4 ≤ Real.exp (-5469477775719/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014738399/1000000000000 : ℝ)/4 ≤ Real.exp ((4497/32768 : ℝ)-(820922270793/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4497/32768 : ℝ) (8995/65536 : ℝ) (820922270793/1000000000000 : ℝ) (2019014738399/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0385; no trusted numerical premise.
theorem cover7_leaf0385_exp_radius : (997551786303936697/1000000000000000000 : ℝ) ≤ Real.exp ((-2249/114688 : ℝ)/8) ∧ Real.exp ((-2249/114688 : ℝ)/8) ≤ (498775893151968349/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2249/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0385_exp_lower : (918089332904125651/1000000000000000000 : ℝ) ≤ Real.exp ((-10938954312253/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938954312253/16000000000000 : ℝ)/8) ≤ (229522333226031413/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938954312253/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0385_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014894769/1000000000000 : ℝ) ≤ 4*Real.exp (8995/65536 : ℝ)*Real.exp (-mu (radius 7 (2249/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014894769/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2249/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0385_exp_radius
  have hrNumeric : (490290648103/500000000000 : ℝ) ≤ Real.exp (-2249/114688 : ℝ) ∧ Real.exp (-2249/114688 : ℝ) ≤ (980581296207/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490290648103/500000000000 : ℝ) ≤ (radius 7 (2249/16384 : ℝ)) ∧ (radius 7 (2249/16384 : ℝ)) ≤ (980581296207/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2249/16384 : ℝ)) (490290648103/500000000000 : ℝ) (980581296207/1000000000000 : ℝ) (49028258133/250000000000 : ℝ) (98056516269/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2249/16384 : ℝ)) (490290648103/500000000000 : ℝ) (980581296207/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490290648103/500000000000 : ℝ) (980581296207/1000000000000 : ℝ) (990290648103/1000000000000 : ℝ) (123786331013/125000000000 : ℝ) (990243049057/1000000000000 : ℝ) (495121524529/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 1 (990290648103/1000000000000 : ℝ) (123786331013/125000000000 : ℝ) (990243049057/1000000000000 : ℝ) (495121524529/500000000000 : ℝ) (49513342429/50000000000 : ℝ) (990266848581/1000000000000 : ℝ) (495133424147/500000000000 : ℝ) (123783356037/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 2 (49513342429/50000000000 : ℝ) (990266848581/1000000000000 : ℝ) (495133424147/500000000000 : ℝ) (123783356037/125000000000 : ℝ) (990266848437/1000000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 3 (990266848437/1000000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 4 (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 5 (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 6 (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2249/16384 : ℝ)) 7 (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2249/16384 : ℝ))) (49028258133/250000000000 : ℝ) (98056516269/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49028258133/250000000000 : ℝ) (98056516269/500000000000 : ℝ) (299028258133/500000000000 : ℝ) (598056516269/1000000000000 : ℝ) (55355813907/125000000000 : ℝ) (13838953477/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 1 (299028258133/500000000000 : ℝ) (598056516269/1000000000000 : ℝ) (55355813907/125000000000 : ℝ) (13838953477/31250000000 : ℝ) (520451513761/1000000000000 : ℝ) (520451513767/1000000000000 : ℝ) (32164569609/62500000000 : ℝ) (514633113751/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 2 (520451513761/1000000000000 : ℝ) (520451513767/1000000000000 : ℝ) (32164569609/62500000000 : ℝ) (514633113751/1000000000000 : ℝ) (64692789219/125000000000 : ℝ) (517542313759/1000000000000 : ℝ) (103506827423/200000000000 : ℝ) (258767068561/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 3 (64692789219/125000000000 : ℝ) (517542313759/1000000000000 : ℝ) (103506827423/200000000000 : ℝ) (258767068561/500000000000 : ℝ) (517538225433/1000000000000 : ℝ) (517538225441/1000000000000 : ℝ) (517538225417/1000000000000 : ℝ) (20701529017/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 4 (517538225433/1000000000000 : ℝ) (517538225441/1000000000000 : ℝ) (517538225417/1000000000000 : ℝ) (20701529017/40000000000 : ℝ) (20701529017/40000000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 5 (20701529017/40000000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 6 (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2249/16384 : ℝ))) 7 (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2249/16384 : ℝ)) hmem 8 (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2249/16384 : ℝ))) hcmem 8 (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2249/16384 : ℝ)) (247566712109/250000000000 : ℝ) (990266848439/1000000000000 : ℝ) (32346139089/62500000000 : ℝ) (517538225433/1000000000000 : ℝ) (164187490423/200000000000 : ℝ) (820937452133/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0385_exp_lower
  have heNumeric : (2019014894769/1000000000000 : ℝ)/4 ≤ Real.exp (-10938954312253/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014894769/1000000000000 : ℝ)/4 ≤ Real.exp ((8995/65536 : ℝ)-(820937452133/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8995/65536 : ℝ) (2249/16384 : ℝ) (820937452133/1000000000000 : ℝ) (2019014894769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0386; no trusted numerical premise.
theorem cover7_leaf0386_exp_radius : (199510302898536581/200000000000000000 : ℝ) ≤ Real.exp ((-8997/458752 : ℝ)/8) ∧ Real.exp ((-8997/458752 : ℝ)/8) ≤ (498775757246341453/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8997/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0386_exp_lower : (918089341921721057/1000000000000000000 : ℝ) ≤ Real.exp ((-546947652751/800000000000 : ℝ)/8) ∧ Real.exp ((-546947652751/800000000000 : ℝ)/8) ≤ (459044670960860529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546947652751/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0386_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009507526709/500000000000 : ℝ) ≤ 4*Real.exp (2249/16384 : ℝ)*Real.exp (-mu (radius 7 (8997/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009507526709/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8997/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0386_exp_radius
  have hrNumeric : (980579158711/1000000000000 : ℝ) ≤ Real.exp (-8997/458752 : ℝ) ∧ Real.exp (-8997/458752 : ℝ) ≤ (122572394839/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980579158711/1000000000000 : ℝ) ≤ (radius 7 (8997/65536 : ℝ)) ∧ (radius 7 (8997/65536 : ℝ)) ≤ (122572394839/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8997/65536 : ℝ)) (980579158711/1000000000000 : ℝ) (122572394839/125000000000 : ℝ) (4903092997/25000000000 : ℝ) (98061859943/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8997/65536 : ℝ)) (980579158711/1000000000000 : ℝ) (122572394839/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980579158711/1000000000000 : ℝ) (122572394839/125000000000 : ℝ) (198057915871/200000000000 : ℝ) (247572394839/250000000000 : ℝ) (495120984889/500000000000 : ℝ) (49512098489/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 1 (198057915871/200000000000 : ℝ) (247572394839/250000000000 : ℝ) (495120984889/500000000000 : ℝ) (49512098489/50000000000 : ℝ) (495132887283/500000000000 : ℝ) (123783221821/125000000000 : ℝ) (24756644357/25000000000 : ℝ) (495132887141/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 2 (495132887283/500000000000 : ℝ) (123783221821/125000000000 : ℝ) (24756644357/25000000000 : ℝ) (495132887141/500000000000 : ℝ) (990265774423/1000000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 3 (990265774423/1000000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 4 (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 5 (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 6 (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8997/65536 : ℝ)) 7 (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8997/65536 : ℝ))) (4903092997/25000000000 : ℝ) (98061859943/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4903092997/25000000000 : ℝ) (98061859943/500000000000 : ℝ) (29903092997/50000000000 : ℝ) (598061859943/1000000000000 : ℝ) (221429288871/500000000000 : ℝ) (1771434311/4000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 1 (29903092997/50000000000 : ℝ) (598061859943/1000000000000 : ℝ) (221429288871/500000000000 : ℝ) (1771434311/4000000000 : ℝ) (520460218841/1000000000000 : ℝ) (520460218847/1000000000000 : ℝ) (51464242411/100000000000 : ℝ) (514642424117/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 2 (520460218841/1000000000000 : ℝ) (520460218847/1000000000000 : ℝ) (51464242411/100000000000 : ℝ) (514642424117/1000000000000 : ℝ) (20702052859/40000000000 : ℝ) (258775660741/500000000000 : ℝ) (517543146681/1000000000000 : ℝ) (517543146689/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 3 (20702052859/40000000000 : ℝ) (258775660741/500000000000 : ℝ) (517543146681/1000000000000 : ℝ) (517543146689/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (258773617043/500000000000 : ℝ) (517547234061/1000000000000 : ℝ) (51754723407/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 4 (258773617039/500000000000 : ℝ) (258773617043/500000000000 : ℝ) (517547234061/1000000000000 : ℝ) (51754723407/100000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 5 (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 6 (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8997/65536 : ℝ))) 7 (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8997/65536 : ℝ)) hmem 8 (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8997/65536 : ℝ))) hcmem 8 (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8997/65536 : ℝ)) (495132887211/500000000000 : ℝ) (39610630977/40000000000 : ℝ) (517547234069/1000000000000 : ℝ) (258773617039/500000000000 : ℝ) (820952632327/1000000000000 : ℝ) (164190526469/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0386_exp_lower
  have heNumeric : (1009507526709/500000000000 : ℝ)/4 ≤ Real.exp (-546947652751/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009507526709/500000000000 : ℝ)/4 ≤ Real.exp ((2249/16384 : ℝ)-(164190526469/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2249/16384 : ℝ) (8997/65536 : ℝ) (164190526469/200000000000 : ℝ) (1009507526709/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0387; no trusted numerical premise.
theorem cover7_leaf0387_exp_radius : (39902049707260127/40000000000000000 : ℝ) ≤ Real.exp ((-4499/229376 : ℝ)/8) ∧ Real.exp ((-4499/229376 : ℝ)/8) ≤ (124693905335187897/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4499/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0387_exp_lower : (183617870213661621/200000000000000000 : ℝ) ≤ Real.exp ((-10938951779803/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938951779803/16000000000000 : ℝ)/8) ≤ (459044675534154053/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938951779803/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0387_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403803042867/200000000000 : ℝ) ≤ 4*Real.exp (8997/65536 : ℝ)*Real.exp (-mu (radius 7 (4499/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403803042867/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4499/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0387_exp_radius
  have hrNumeric : (49028851061/50000000000 : ℝ) ≤ Real.exp (-4499/229376 : ℝ) ∧ Real.exp (-4499/229376 : ℝ) ≤ (980577021221/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49028851061/50000000000 : ℝ) ≤ (radius 7 (4499/32768 : ℝ)) ∧ (radius 7 (4499/32768 : ℝ)) ≤ (980577021221/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4499/32768 : ℝ)) (49028851061/50000000000 : ℝ) (980577021221/1000000000000 : ℝ) (98067203301/500000000000 : ℝ) (12258400413/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4499/32768 : ℝ)) (49028851061/50000000000 : ℝ) (980577021221/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49028851061/50000000000 : ℝ) (980577021221/1000000000000 : ℝ) (99028851061/100000000000 : ℝ) (990288510611/1000000000000 : ℝ) (1980481781/2000000000 : ℝ) (495120445251/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 1 (99028851061/100000000000 : ℝ) (990288510611/1000000000000 : ℝ) (1980481781/2000000000 : ℝ) (495120445251/500000000000 : ℝ) (198052940111/200000000000 : ℝ) (990264700557/1000000000000 : ℝ) (247566175067/250000000000 : ℝ) (990264700271/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 2 (198052940111/200000000000 : ℝ) (990264700557/1000000000000 : ℝ) (247566175067/250000000000 : ℝ) (990264700271/1000000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 3 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 4 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 5 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 6 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4499/32768 : ℝ)) 7 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4499/32768 : ℝ))) (98067203301/500000000000 : ℝ) (12258400413/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98067203301/500000000000 : ℝ) (12258400413/62500000000 : ℝ) (598067203301/1000000000000 : ℝ) (74758400413/125000000000 : ℝ) (55358830399/125000000000 : ℝ) (34599269/78125000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 1 (598067203301/1000000000000 : ℝ) (74758400413/125000000000 : ℝ) (55358830399/125000000000 : ℝ) (34599269/78125000 : ℝ) (260234461623/500000000000 : ℝ) (130117230813/250000000000 : ℝ) (514651733697/1000000000000 : ℝ) (64331466713/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 2 (260234461623/500000000000 : ℝ) (130117230813/250000000000 : ℝ) (514651733697/1000000000000 : ℝ) (64331466713/125000000000 : ℝ) (517560328471/1000000000000 : ℝ) (258780164239/500000000000 : ℝ) (808675243/1562500000 : ℝ) (64694019441/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 3 (517560328471/1000000000000 : ℝ) (258780164239/500000000000 : ℝ) (808675243/1562500000 : ℝ) (64694019441/125000000000 : ℝ) (103511248399/200000000000 : ℝ) (517556242003/1000000000000 : ℝ) (517556241979/1000000000000 : ℝ) (517556241987/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 4 (103511248399/200000000000 : ℝ) (517556242003/1000000000000 : ℝ) (517556241979/1000000000000 : ℝ) (517556241987/1000000000000 : ℝ) (517556241987/1000000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 5 (517556241987/1000000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 6 (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4499/32768 : ℝ))) 7 (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4499/32768 : ℝ)) hmem 8 (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4499/32768 : ℝ))) hcmem 8 (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4499/32768 : ℝ)) (990264700411/1000000000000 : ℝ) (495132350207/500000000000 : ℝ) (258778120993/500000000000 : ℝ) (103511248399/200000000000 : ℝ) (164193562283/200000000000 : ℝ) (820967811433/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0387_exp_lower
  have heNumeric : (403803042867/200000000000 : ℝ)/4 ≤ Real.exp (-10938951779803/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403803042867/200000000000 : ℝ)/4 ≤ Real.exp ((8997/65536 : ℝ)-(820967811433/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8997/65536 : ℝ) (4499/32768 : ℝ) (820967811433/1000000000000 : ℝ) (403803042867/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0388; no trusted numerical premise.
theorem cover7_leaf0388_exp_radius : (249387742717599377/250000000000000000 : ℝ) ≤ Real.exp ((-8999/458752 : ℝ)/8) ∧ Real.exp ((-8999/458752 : ℝ)/8) ≤ (997550970870397509/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8999/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0388_exp_lower : (2295223400859717/2500000000000000 : ℝ) ≤ Real.exp ((-5469475243301/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469475243301/8000000000000 : ℝ)/8) ≤ (918089360343886801/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469475243301/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0388_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009507688761/500000000000 : ℝ) ≤ 4*Real.exp (4499/32768 : ℝ)*Real.exp (-mu (radius 7 (8999/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009507688761/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8999/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0388_exp_radius
  have hrNumeric : (490287441867/500000000000 : ℝ) ≤ Real.exp (-8999/458752 : ℝ) ∧ Real.exp (-8999/458752 : ℝ) ≤ (196114976747/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490287441867/500000000000 : ℝ) ≤ (radius 7 (8999/65536 : ℝ)) ∧ (radius 7 (8999/65536 : ℝ)) ≤ (196114976747/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8999/65536 : ℝ)) (490287441867/500000000000 : ℝ) (196114976747/200000000000 : ℝ) (98072546347/500000000000 : ℝ) (1961450927/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8999/65536 : ℝ)) (490287441867/500000000000 : ℝ) (196114976747/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490287441867/500000000000 : ℝ) (196114976747/200000000000 : ℝ) (990287441867/1000000000000 : ℝ) (247571860467/250000000000 : ℝ) (123779976403/125000000000 : ℝ) (495119905613/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 1 (990287441867/1000000000000 : ℝ) (247571860467/250000000000 : ℝ) (123779976403/125000000000 : ℝ) (495119905613/500000000000 : ℝ) (198052725309/200000000000 : ℝ) (990263626547/1000000000000 : ℝ) (990263626259/1000000000000 : ℝ) (990263626261/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 2 (198052725309/200000000000 : ℝ) (990263626547/1000000000000 : ℝ) (990263626259/1000000000000 : ℝ) (990263626261/1000000000000 : ℝ) (495131813201/500000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 3 (495131813201/500000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 4 (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 5 (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 6 (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8999/65536 : ℝ)) 7 (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8999/65536 : ℝ))) (98072546347/500000000000 : ℝ) (1961450927/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98072546347/500000000000 : ℝ) (1961450927/10000000000 : ℝ) (598072546347/1000000000000 : ℝ) (11961450927/20000000000 : ℝ) (442882707603/1000000000000 : ℝ) (442882707611/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 1 (598072546347/1000000000000 : ℝ) (11961450927/20000000000 : ℝ) (442882707603/1000000000000 : ℝ) (442882707611/1000000000000 : ℝ) (20819105079/40000000000 : ℝ) (520477626981/1000000000000 : ℝ) (514661042501/1000000000000 : ℝ) (128665260627/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 2 (20819105079/40000000000 : ℝ) (520477626981/1000000000000 : ℝ) (514661042501/1000000000000 : ℝ) (128665260627/250000000000 : ℝ) (258784667369/500000000000 : ℝ) (103513866949/200000000000 : ℝ) (517561163629/1000000000000 : ℝ) (129390290909/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 3 (258784667369/500000000000 : ℝ) (103513866949/200000000000 : ℝ) (517561163629/1000000000000 : ℝ) (129390290909/250000000000 : ℝ) (517565249183/1000000000000 : ℝ) (517565249191/1000000000000 : ℝ) (517565249167/1000000000000 : ℝ) (20702609967/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 4 (517565249183/1000000000000 : ℝ) (517565249191/1000000000000 : ℝ) (517565249167/1000000000000 : ℝ) (20702609967/40000000000 : ℝ) (20702609967/40000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 5 (20702609967/40000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 6 (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8999/65536 : ℝ))) 7 (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8999/65536 : ℝ)) hmem 8 (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8999/65536 : ℝ))) hcmem 8 (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8999/65536 : ℝ)) (990263626401/1000000000000 : ℝ) (247565906601/250000000000 : ℝ) (258782624587/500000000000 : ℝ) (517565249183/1000000000000 : ℝ) (820982989379/1000000000000 : ℝ) (820982989397/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0388_exp_lower
  have heNumeric : (1009507688761/500000000000 : ℝ)/4 ≤ Real.exp (-5469475243301/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009507688761/500000000000 : ℝ)/4 ≤ Real.exp ((4499/32768 : ℝ)-(820982989397/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4499/32768 : ℝ) (8999/65536 : ℝ) (820982989397/1000000000000 : ℝ) (1009507688761/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0389; no trusted numerical premise.
theorem cover7_leaf0389_exp_radius : (997550699059365903/1000000000000000000 : ℝ) ≤ Real.exp ((-1125/57344 : ℝ)/8) ∧ Real.exp ((-1125/57344 : ℝ)/8) ≤ (62346918691210369/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1125/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0389_exp_lower : (918089369749145711/1000000000000000000 : ℝ) ≤ Real.exp ((-10938949175321/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938949175321/16000000000000 : ℝ)/8) ≤ (57380585609321607/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938949175321/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0389_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019015542991/1000000000000 : ℝ) ≤ 4*Real.exp (8999/65536 : ℝ)*Real.exp (-mu (radius 7 (1125/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019015542991/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1125/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0389_exp_radius
  have hrNumeric : (980572746253/1000000000000 : ℝ) ≤ Real.exp (-1125/57344 : ℝ) ∧ Real.exp (-1125/57344 : ℝ) ≤ (490286373127/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980572746253/1000000000000 : ℝ) ≤ (radius 7 (1125/8192 : ℝ)) ∧ (radius 7 (1125/8192 : ℝ)) ≤ (490286373127/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1125/8192 : ℝ)) (980572746253/1000000000000 : ℝ) (490286373127/500000000000 : ℝ) (39231155631/200000000000 : ℝ) (196155778161/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1125/8192 : ℝ)) (980572746253/1000000000000 : ℝ) (490286373127/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980572746253/1000000000000 : ℝ) (490286373127/500000000000 : ℝ) (495143186563/500000000000 : ℝ) (990286373127/1000000000000 : ℝ) (990238731949/1000000000000 : ℝ) (990238731951/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 1 (495143186563/500000000000 : ℝ) (990286373127/1000000000000 : ℝ) (990238731949/1000000000000 : ℝ) (990238731951/1000000000000 : ℝ) (990262552537/1000000000000 : ℝ) (990262552539/1000000000000 : ℝ) (990262552251/1000000000000 : ℝ) (990262552253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 2 (990262552537/1000000000000 : ℝ) (990262552539/1000000000000 : ℝ) (990262552251/1000000000000 : ℝ) (990262552253/1000000000000 : ℝ) (495131276197/500000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 3 (495131276197/500000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 4 (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 5 (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 6 (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1125/8192 : ℝ)) 7 (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1125/8192 : ℝ))) (39231155631/200000000000 : ℝ) (196155778161/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39231155631/200000000000 : ℝ) (196155778161/1000000000000 : ℝ) (598077889077/1000000000000 : ℝ) (598077889081/1000000000000 : ℝ) (110723692743/250000000000 : ℝ) (22144738549/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 1 (598077889077/1000000000000 : ℝ) (598077889081/1000000000000 : ℝ) (110723692743/250000000000 : ℝ) (22144738549/50000000000 : ℝ) (65060791253/125000000000 : ℝ) (520486330031/1000000000000 : ℝ) (514670350521/1000000000000 : ℝ) (514670350529/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 2 (65060791253/125000000000 : ℝ) (520486330031/1000000000000 : ℝ) (514670350521/1000000000000 : ℝ) (514670350529/1000000000000 : ℝ) (32348646267/62500000000 : ℝ) (12939458507/25000000000 : ℝ) (103514034201/200000000000 : ℝ) (258785085507/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 3 (32348646267/62500000000 : ℝ) (12939458507/25000000000 : ℝ) (103514034201/200000000000 : ℝ) (258785085507/500000000000 : ℝ) (258787127819/500000000000 : ℝ) (517574255647/1000000000000 : ℝ) (258787127811/500000000000 : ℝ) (517574255631/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 4 (258787127819/500000000000 : ℝ) (517574255647/1000000000000 : ℝ) (258787127811/500000000000 : ℝ) (517574255631/1000000000000 : ℝ) (51757425563/100000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 5 (51757425563/100000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 6 (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1125/8192 : ℝ))) 7 (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1125/8192 : ℝ)) hmem 8 (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1125/8192 : ℝ))) hcmem 8 (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1125/8192 : ℝ)) (990262552393/1000000000000 : ℝ) (247565638099/250000000000 : ℝ) (517574255629/1000000000000 : ℝ) (517574255639/1000000000000 : ℝ) (205249541553/250000000000 : ℝ) (820998166231/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0389_exp_lower
  have heNumeric : (2019015542991/1000000000000 : ℝ)/4 ≤ Real.exp (-10938949175321/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019015542991/1000000000000 : ℝ)/4 ≤ Real.exp ((8999/65536 : ℝ)-(820998166231/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8999/65536 : ℝ) (1125/8192 : ℝ) (820998166231/1000000000000 : ℝ) (2019015542991/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0390; no trusted numerical premise.
theorem cover7_leaf0390_exp_radius : (997550427248408361/1000000000000000000 : ℝ) ≤ Real.exp ((-9001/458752 : ℝ)/8) ∧ Real.exp ((-9001/458752 : ℝ)/8) ≤ (498775213624204181/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9001/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0390_exp_lower : (459044689641927661/500000000000000000 : ℝ) ≤ Real.exp ((-1367368480749/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367368480749/2000000000000 : ℝ)/8) ≤ (918089379283855323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367368480749/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0390_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019015710737/1000000000000 : ℝ) ≤ 4*Real.exp (1125/8192 : ℝ)*Real.exp (-mu (radius 7 (9001/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019015710737/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9001/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0390_exp_radius
  have hrNumeric : (980570608777/1000000000000 : ℝ) ≤ Real.exp (-9001/458752 : ℝ) ∧ Real.exp (-9001/458752 : ℝ) ≤ (490285304389/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980570608777/1000000000000 : ℝ) ≤ (radius 7 (9001/65536 : ℝ)) ∧ (radius 7 (9001/65536 : ℝ)) ≤ (490285304389/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9001/65536 : ℝ)) (980570608777/1000000000000 : ℝ) (490285304389/500000000000 : ℝ) (98083231493/500000000000 : ℝ) (12260403937/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9001/65536 : ℝ)) (980570608777/1000000000000 : ℝ) (490285304389/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980570608777/1000000000000 : ℝ) (490285304389/500000000000 : ℝ) (247571326097/250000000000 : ℝ) (990285304389/1000000000000 : ℝ) (39609506107/40000000000 : ℝ) (990237652677/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 1 (247571326097/250000000000 : ℝ) (990285304389/1000000000000 : ℝ) (39609506107/40000000000 : ℝ) (990237652677/1000000000000 : ℝ) (990261478531/1000000000000 : ℝ) (990261478533/1000000000000 : ℝ) (247565369561/250000000000 : ℝ) (990261478247/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 2 (990261478531/1000000000000 : ℝ) (990261478533/1000000000000 : ℝ) (247565369561/250000000000 : ℝ) (990261478247/1000000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 3 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 4 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 5 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 6 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9001/65536 : ℝ)) 7 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9001/65536 : ℝ))) (98083231493/500000000000 : ℝ) (12260403937/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98083231493/500000000000 : ℝ) (12260403937/62500000000 : ℝ) (598083231493/1000000000000 : ℝ) (74760403937/125000000000 : ℝ) (221453416651/500000000000 : ℝ) (44290683331/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 1 (598083231493/1000000000000 : ℝ) (74760403937/125000000000 : ℝ) (221453416651/500000000000 : ℝ) (44290683331/100000000000 : ℝ) (520495032397/1000000000000 : ℝ) (520495032403/1000000000000 : ℝ) (514679657759/1000000000000 : ℝ) (257339828883/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 2 (520495032397/1000000000000 : ℝ) (520495032403/1000000000000 : ℝ) (514679657759/1000000000000 : ℝ) (257339828883/500000000000 : ℝ) (258793672539/500000000000 : ℝ) (103517469017/200000000000 : ℝ) (129394794413/250000000000 : ℝ) (517579177659/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 3 (258793672539/500000000000 : ℝ) (103517469017/200000000000 : ℝ) (129394794413/250000000000 : ℝ) (517579177659/1000000000000 : ℝ) (103516652273/200000000000 : ℝ) (129395815343/250000000000 : ℝ) (129395815337/250000000000 : ℝ) (129395815339/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 4 (103516652273/200000000000 : ℝ) (129395815343/250000000000 : ℝ) (129395815337/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 5 (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 6 (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9001/65536 : ℝ))) 7 (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9001/65536 : ℝ)) hmem 8 (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9001/65536 : ℝ))) hcmem 8 (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9001/65536 : ℝ)) (990261478387/1000000000000 : ℝ) (99026147839/100000000000 : ℝ) (129395815339/250000000000 : ℝ) (129395815341/250000000000 : ℝ) (5131333387/6250000000 : ℝ) (821013341937/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0390_exp_lower
  have heNumeric : (2019015710737/1000000000000 : ℝ)/4 ≤ Real.exp (-1367368480749/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019015710737/1000000000000 : ℝ)/4 ≤ Real.exp ((1125/8192 : ℝ)-(821013341937/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1125/8192 : ℝ) (9001/65536 : ℝ) (821013341937/1000000000000 : ℝ) (2019015710737/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0391; no trusted numerical premise.
theorem cover7_leaf0391_exp_radius : (498775077718762441/500000000000000000 : ℝ) ≤ Real.exp ((-643/32768 : ℝ)/8) ∧ Real.exp ((-643/32768 : ℝ)/8) ≤ (997550155437524883/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-643/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0391_exp_lower : (183617877789419509/200000000000000000 : ℝ) ≤ Real.exp ((-10938946498743/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938946498743/16000000000000 : ℝ)/8) ≤ (459044694473548773/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938946498743/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0391_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376985093/125000000000 : ℝ) ≤ 4*Real.exp (9001/65536 : ℝ)*Real.exp (-mu (radius 7 (4501/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376985093/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4501/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0391_exp_radius
  have hrNumeric : (196113694261/200000000000 : ℝ) ≤ Real.exp (-643/32768 : ℝ) ∧ Real.exp (-643/32768 : ℝ) ≤ (490284235653/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196113694261/200000000000 : ℝ) ≤ (radius 7 (4501/32768 : ℝ)) ∧ (radius 7 (4501/32768 : ℝ)) ≤ (490284235653/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4501/32768 : ℝ)) (196113694261/200000000000 : ℝ) (490284235653/500000000000 : ℝ) (24522143399/125000000000 : ℝ) (98088573599/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4501/32768 : ℝ)) (196113694261/200000000000 : ℝ) (490284235653/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196113694261/200000000000 : ℝ) (490284235653/500000000000 : ℝ) (247571058913/250000000000 : ℝ) (990284235653/1000000000000 : ℝ) (990236573403/1000000000000 : ℝ) (247559143351/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 1 (247571058913/250000000000 : ℝ) (990284235653/1000000000000 : ℝ) (990236573403/1000000000000 : ℝ) (247559143351/250000000000 : ℝ) (990260404527/1000000000000 : ℝ) (990260404529/1000000000000 : ℝ) (12378255053/12500000000 : ℝ) (495130202121/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 2 (990260404527/1000000000000 : ℝ) (990260404529/1000000000000 : ℝ) (12378255053/12500000000 : ℝ) (495130202121/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 3 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 4 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 5 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 6 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4501/32768 : ℝ)) 7 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4501/32768 : ℝ))) (24522143399/125000000000 : ℝ) (98088573599/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24522143399/125000000000 : ℝ) (98088573599/500000000000 : ℝ) (149522143399/250000000000 : ℝ) (598088573599/1000000000000 : ℝ) (221459447299/500000000000 : ℝ) (88583778921/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 1 (149522143399/250000000000 : ℝ) (598088573599/1000000000000 : ℝ) (221459447299/500000000000 : ℝ) (88583778921/200000000000 : ℝ) (520503734097/1000000000000 : ℝ) (260251867051/500000000000 : ℝ) (514688964219/1000000000000 : ℝ) (20587558569/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 2 (520503734097/1000000000000 : ℝ) (260251867051/500000000000 : ℝ) (514688964219/1000000000000 : ℝ) (20587558569/40000000000 : ℝ) (258798174579/500000000000 : ℝ) (129399087291/250000000000 : ℝ) (517588183573/1000000000000 : ℝ) (517588183579/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 3 (258798174579/500000000000 : ℝ) (129399087291/250000000000 : ℝ) (517588183573/1000000000000 : ℝ) (517588183579/1000000000000 : ℝ) (103518453273/200000000000 : ℝ) (129398066593/250000000000 : ℝ) (517592266349/1000000000000 : ℝ) (129398066589/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 4 (103518453273/200000000000 : ℝ) (129398066593/250000000000 : ℝ) (517592266349/1000000000000 : ℝ) (129398066589/250000000000 : ℝ) (517592266357/1000000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 5 (517592266357/1000000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 6 (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4501/32768 : ℝ))) 7 (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4501/32768 : ℝ)) hmem 8 (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4501/32768 : ℝ))) hcmem 8 (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4501/32768 : ℝ)) (990260404383/1000000000000 : ℝ) (495130202193/500000000000 : ℝ) (129398066589/250000000000 : ℝ) (129398066591/250000000000 : ℝ) (821028516507/1000000000000 : ℝ) (821028516523/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0391_exp_lower
  have heNumeric : (252376985093/125000000000 : ℝ)/4 ≤ Real.exp (-10938946498743/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376985093/125000000000 : ℝ)/4 ≤ Real.exp ((9001/65536 : ℝ)-(821028516523/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9001/65536 : ℝ) (4501/32768 : ℝ) (821028516523/1000000000000 : ℝ) (252376985093/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0392; no trusted numerical premise.
theorem cover7_leaf0392_exp_radius : (498774941813357733/500000000000000000 : ℝ) ≤ Real.exp ((-9003/458752 : ℝ)/8) ∧ Real.exp ((-9003/458752 : ℝ)/8) ≤ (997549883626715467/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9003/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0392_exp_lower : (183617879747728573/200000000000000000 : ℝ) ≤ Real.exp ((-5469472566803/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469472566803/8000000000000 : ℝ)/8) ≤ (459044699369321433/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469472566803/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0392_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016053009/1000000000000 : ℝ) ≤ 4*Real.exp (4501/32768 : ℝ)*Real.exp (-mu (radius 7 (9003/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016053009/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9003/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0392_exp_radius
  have hrNumeric : (980566333837/1000000000000 : ℝ) ≤ Real.exp (-9003/458752 : ℝ) ∧ Real.exp (-9003/458752 : ℝ) ≤ (490283166919/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980566333837/1000000000000 : ℝ) ≤ (radius 7 (9003/65536 : ℝ)) ∧ (radius 7 (9003/65536 : ℝ)) ≤ (490283166919/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9003/65536 : ℝ)) (980566333837/1000000000000 : ℝ) (490283166919/500000000000 : ℝ) (196187830773/1000000000000 : ℝ) (196187830779/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9003/65536 : ℝ)) (980566333837/1000000000000 : ℝ) (490283166919/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980566333837/1000000000000 : ℝ) (490283166919/500000000000 : ℝ) (495141583459/500000000000 : ℝ) (990283166919/1000000000000 : ℝ) (990235494131/1000000000000 : ℝ) (247558873533/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 1 (495141583459/500000000000 : ℝ) (990283166919/1000000000000 : ℝ) (990235494131/1000000000000 : ℝ) (247558873533/250000000000 : ℝ) (247564832631/250000000000 : ℝ) (495129665263/500000000000 : ℝ) (990259330237/1000000000000 : ℝ) (990259330239/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 2 (247564832631/250000000000 : ℝ) (495129665263/500000000000 : ℝ) (990259330237/1000000000000 : ℝ) (990259330239/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 3 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 4 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 5 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 6 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9003/65536 : ℝ)) 7 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9003/65536 : ℝ))) (196187830773/1000000000000 : ℝ) (196187830779/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196187830773/1000000000000 : ℝ) (196187830779/1000000000000 : ℝ) (299046957693/500000000000 : ℝ) (59809391539/100000000000 : ℝ) (442930954859/1000000000000 : ℝ) (442930954867/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 1 (299046957693/500000000000 : ℝ) (59809391539/100000000000 : ℝ) (442930954859/1000000000000 : ℝ) (442930954867/1000000000000 : ℝ) (260256217561/500000000000 : ℝ) (520512435129/1000000000000 : ℝ) (514698269899/1000000000000 : ℝ) (257349134953/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 2 (260256217561/500000000000 : ℝ) (520512435129/1000000000000 : ℝ) (514698269899/1000000000000 : ℝ) (257349134953/500000000000 : ℝ) (51760535251/100000000000 : ℝ) (258802676259/500000000000 : ℝ) (103519437753/200000000000 : ℝ) (517597188773/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 3 (51760535251/100000000000 : ℝ) (258802676259/500000000000 : ℝ) (103519437753/200000000000 : ℝ) (517597188773/1000000000000 : ℝ) (517601270637/1000000000000 : ℝ) (258800635323/500000000000 : ℝ) (517601270621/1000000000000 : ℝ) (51760127063/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 4 (517601270637/1000000000000 : ℝ) (258800635323/500000000000 : ℝ) (517601270621/1000000000000 : ℝ) (51760127063/100000000000 : ℝ) (517601270629/1000000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 5 (517601270629/1000000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 6 (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9003/65536 : ℝ))) 7 (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9003/65536 : ℝ)) hmem 8 (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9003/65536 : ℝ))) hcmem 8 (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9003/65536 : ℝ)) (49512966519/50000000000 : ℝ) (990259330383/1000000000000 : ℝ) (129400317657/250000000000 : ℝ) (258800635319/500000000000 : ℝ) (821043689971/1000000000000 : ℝ) (821043689991/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0392_exp_lower
  have heNumeric : (2019016053009/1000000000000 : ℝ)/4 ≤ Real.exp (-5469472566803/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016053009/1000000000000 : ℝ)/4 ≤ Real.exp ((4501/32768 : ℝ)-(821043689991/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4501/32768 : ℝ) (9003/65536 : ℝ) (821043689991/1000000000000 : ℝ) (2019016053009/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0393; no trusted numerical premise.
theorem cover7_leaf0393_exp_radius : (997549611815980111/1000000000000000000 : ℝ) ≤ Real.exp ((-2251/114688 : ℝ)/8) ∧ Real.exp ((-2251/114688 : ℝ)/8) ≤ (62346850738498757/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2251/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0393_exp_lower : (183617881732134349/200000000000000000 : ℝ) ≤ Real.exp ((-10938943750277/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938943750277/16000000000000 : ℝ)/8) ≤ (459044704330335873/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938943750277/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0393_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016227569/1000000000000 : ℝ) ≤ 4*Real.exp (9003/65536 : ℝ)*Real.exp (-mu (radius 7 (2251/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016227569/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2251/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0393_exp_radius
  have hrNumeric : (7844513571/8000000000 : ℝ) ≤ Real.exp (-2251/114688 : ℝ) ∧ Real.exp (-2251/114688 : ℝ) ≤ (122570524547/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7844513571/8000000000 : ℝ) ≤ (radius 7 (2251/16384 : ℝ)) ∧ (radius 7 (2251/16384 : ℝ)) ≤ (122570524547/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2251/16384 : ℝ)) (7844513571/8000000000 : ℝ) (122570524547/125000000000 : ℝ) (98099256859/500000000000 : ℝ) (49049628431/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2251/16384 : ℝ)) (7844513571/8000000000 : ℝ) (122570524547/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7844513571/8000000000 : ℝ) (122570524547/125000000000 : ℝ) (990282098187/1000000000000 : ℝ) (247570524547/250000000000 : ℝ) (49511720743/50000000000 : ℝ) (495117207431/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 1 (990282098187/1000000000000 : ℝ) (247570524547/250000000000 : ℝ) (49511720743/50000000000 : ℝ) (495117207431/500000000000 : ℝ) (990258256523/1000000000000 : ℝ) (39610330261/40000000000 : ℝ) (247564564059/250000000000 : ℝ) (495129128119/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 2 (990258256523/1000000000000 : ℝ) (39610330261/40000000000 : ℝ) (247564564059/250000000000 : ℝ) (495129128119/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 3 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 4 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 5 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 6 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2251/16384 : ℝ)) 7 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2251/16384 : ℝ))) (98099256859/500000000000 : ℝ) (49049628431/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98099256859/500000000000 : ℝ) (49049628431/250000000000 : ℝ) (598099256859/1000000000000 : ℝ) (299049628431/500000000000 : ℝ) (17717720563/40000000000 : ℝ) (221471507041/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 1 (598099256859/1000000000000 : ℝ) (299049628431/500000000000 : ℝ) (17717720563/40000000000 : ℝ) (221471507041/500000000000 : ℝ) (520521135467/1000000000000 : ℝ) (32532570967/62500000000 : ℝ) (64338446849/125000000000 : ℝ) (514707574799/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 2 (520521135467/1000000000000 : ℝ) (32532570967/62500000000 : ℝ) (64338446849/125000000000 : ℝ) (514707574799/1000000000000 : ℝ) (517614355129/1000000000000 : ℝ) (8087724299/15625000000 : ℝ) (64700774153/125000000000 : ℝ) (517606193231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 3 (517614355129/1000000000000 : ℝ) (8087724299/15625000000 : ℝ) (64700774153/125000000000 : ℝ) (517606193231/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (64701284273/125000000000 : ℝ) (6470128427/12500000000 : ℝ) (64701284271/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 4 (4043830267/7812500000 : ℝ) (64701284273/125000000000 : ℝ) (6470128427/12500000000 : ℝ) (64701284271/125000000000 : ℝ) (64701284271/125000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 5 (64701284271/125000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 6 (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2251/16384 : ℝ))) 7 (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2251/16384 : ℝ)) hmem 8 (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2251/16384 : ℝ))) hcmem 8 (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2251/16384 : ℝ)) (990258256379/1000000000000 : ℝ) (495129128191/500000000000 : ℝ) (517610274167/1000000000000 : ℝ) (4043830267/7812500000 : ℝ) (25658089447/31250000000 : ℝ) (410529431161/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0393_exp_lower
  have heNumeric : (2019016227569/1000000000000 : ℝ)/4 ≤ Real.exp (-10938943750277/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016227569/1000000000000 : ℝ)/4 ≤ Real.exp ((9003/65536 : ℝ)-(410529431161/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9003/65536 : ℝ) (2251/16384 : ℝ) (410529431161/500000000000 : ℝ) (2019016227569/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0394; no trusted numerical premise.
theorem cover7_leaf0394_exp_radius : (49877467000265941/50000000000000000 : ℝ) ≤ Real.exp ((-9005/458752 : ℝ)/8) ∧ Real.exp ((-9005/458752 : ℝ)/8) ≤ (997549340005318821/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9005/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0394_exp_lower : (918089418711118491/1000000000000000000 : ℝ) ≤ Real.exp ((-2734735587261/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734735587261/4000000000000 : ℝ)/8) ≤ (229522354677779623/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734735587261/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0394_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016404389/1000000000000 : ℝ) ≤ 4*Real.exp (2251/16384 : ℝ)*Real.exp (-mu (radius 7 (9005/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016404389/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9005/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0394_exp_radius
  have hrNumeric : (980562058917/1000000000000 : ℝ) ≤ Real.exp (-9005/458752 : ℝ) ∧ Real.exp (-9005/458752 : ℝ) ≤ (490281029459/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980562058917/1000000000000 : ℝ) ≤ (radius 7 (9005/65536 : ℝ)) ∧ (radius 7 (9005/65536 : ℝ)) ≤ (490281029459/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9005/65536 : ℝ)) (980562058917/1000000000000 : ℝ) (490281029459/500000000000 : ℝ) (196209196039/1000000000000 : ℝ) (39241839209/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9005/65536 : ℝ)) (980562058917/1000000000000 : ℝ) (490281029459/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980562058917/1000000000000 : ℝ) (490281029459/500000000000 : ℝ) (495140514729/500000000000 : ℝ) (990281029459/1000000000000 : ℝ) (990233335591/1000000000000 : ℝ) (990233335593/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 1 (495140514729/500000000000 : ℝ) (990281029459/1000000000000 : ℝ) (990233335591/1000000000000 : ℝ) (990233335593/1000000000000 : ℝ) (247564295631/250000000000 : ℝ) (495128591263/500000000000 : ℝ) (990257182237/1000000000000 : ℝ) (990257182239/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 2 (247564295631/250000000000 : ℝ) (495128591263/500000000000 : ℝ) (990257182237/1000000000000 : ℝ) (990257182239/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 3 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 4 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 5 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 6 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9005/65536 : ℝ)) 7 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9005/65536 : ℝ))) (196209196039/1000000000000 : ℝ) (39241839209/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196209196039/1000000000000 : ℝ) (39241839209/200000000000 : ℝ) (598104598019/1000000000000 : ℝ) (598104598023/1000000000000 : ℝ) (442955072257/1000000000000 : ℝ) (88591014453/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 1 (598104598019/1000000000000 : ℝ) (598104598023/1000000000000 : ℝ) (442955072257/1000000000000 : ℝ) (88591014453/200000000000 : ℝ) (260264917569/500000000000 : ℝ) (65066229393/125000000000 : ℝ) (514716878907/1000000000000 : ℝ) (102943375783/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 2 (260264917569/500000000000 : ℝ) (65066229393/125000000000 : ℝ) (514716878907/1000000000000 : ℝ) (102943375783/200000000000 : ℝ) (258811678511/500000000000 : ℝ) (51762335703/100000000000 : ℝ) (129403799239/250000000000 : ℝ) (129403799241/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 3 (258811678511/500000000000 : ℝ) (51762335703/100000000000 : ℝ) (129403799239/250000000000 : ℝ) (129403799241/250000000000 : ℝ) (517619276989/1000000000000 : ℝ) (517619276997/1000000000000 : ℝ) (129404819243/250000000000 : ℝ) (517619276981/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 4 (517619276989/1000000000000 : ℝ) (517619276997/1000000000000 : ℝ) (129404819243/250000000000 : ℝ) (517619276981/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 5 (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 6 (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9005/65536 : ℝ))) 7 (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9005/65536 : ℝ)) hmem 8 (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9005/65536 : ℝ))) hcmem 8 (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9005/65536 : ℝ)) (49512859119/50000000000 : ℝ) (990257182383/1000000000000 : ℝ) (25880963849/50000000000 : ℝ) (517619276989/1000000000000 : ℝ) (821074033517/1000000000000 : ℝ) (410537016767/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0394_exp_lower
  have heNumeric : (2019016404389/1000000000000 : ℝ)/4 ≤ Real.exp (-2734735587261/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016404389/1000000000000 : ℝ)/4 ≤ Real.exp ((2251/16384 : ℝ)-(410537016767/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2251/16384 : ℝ) (9005/65536 : ℝ) (410537016767/500000000000 : ℝ) (2019016404389/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0395; no trusted numerical premise.
theorem cover7_leaf0395_exp_radius : (997549068194731591/1000000000000000000 : ℝ) ≤ Real.exp ((-4503/229376 : ℝ)/8) ∧ Real.exp ((-4503/229376 : ℝ)/8) ≤ (124693633524341449/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4503/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0395_exp_lower : (183617885777996621/200000000000000000 : ℝ) ≤ Real.exp ((-10938940929907/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938940929907/16000000000000 : ℝ)/8) ≤ (459044714444991553/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938940929907/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0395_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016583467/1000000000000 : ℝ) ≤ 4*Real.exp (9005/65536 : ℝ)*Real.exp (-mu (radius 7 (4503/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016583467/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4503/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0395_exp_radius
  have hrNumeric : (980559921463/1000000000000 : ℝ) ≤ Real.exp (-4503/229376 : ℝ) ∧ Real.exp (-4503/229376 : ℝ) ≤ (122569990183/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980559921463/1000000000000 : ℝ) ≤ (radius 7 (4503/32768 : ℝ)) ∧ (radius 7 (4503/32768 : ℝ)) ≤ (122569990183/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4503/32768 : ℝ)) (980559921463/1000000000000 : ℝ) (122569990183/125000000000 : ℝ) (39243975547/200000000000 : ℝ) (196219877741/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4503/32768 : ℝ)) (980559921463/1000000000000 : ℝ) (122569990183/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980559921463/1000000000000 : ℝ) (122569990183/125000000000 : ℝ) (990279960731/1000000000000 : ℝ) (247569990183/250000000000 : ℝ) (990232256323/1000000000000 : ℝ) (247558064081/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 1 (990279960731/1000000000000 : ℝ) (247569990183/250000000000 : ℝ) (990232256323/1000000000000 : ℝ) (247558064081/250000000000 : ℝ) (990256108527/1000000000000 : ℝ) (61891006783/62500000000 : ℝ) (990256108239/1000000000000 : ℝ) (990256108241/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 2 (990256108527/1000000000000 : ℝ) (61891006783/62500000000 : ℝ) (990256108239/1000000000000 : ℝ) (990256108241/1000000000000 : ℝ) (990256108383/1000000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 3 (990256108383/1000000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 4 (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 5 (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 6 (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4503/32768 : ℝ)) 7 (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4503/32768 : ℝ))) (39243975547/200000000000 : ℝ) (196219877741/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39243975547/200000000000 : ℝ) (196219877741/1000000000000 : ℝ) (598109938867/1000000000000 : ℝ) (598109938871/1000000000000 : ℝ) (221483564703/500000000000 : ℝ) (221483564707/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 1 (598109938867/1000000000000 : ℝ) (598109938871/1000000000000 : ℝ) (221483564703/500000000000 : ℝ) (221483564707/500000000000 : ℝ) (65067316767/125000000000 : ℝ) (520538534143/1000000000000 : ℝ) (102945236449/200000000000 : ℝ) (128681545563/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 2 (65067316767/125000000000 : ℝ) (520538534143/1000000000000 : ℝ) (102945236449/200000000000 : ℝ) (128681545563/250000000000 : ℝ) (51763235819/100000000000 : ℝ) (258816179099/500000000000 : ℝ) (258812099981/500000000000 : ℝ) (51762419997/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 3 (51763235819/100000000000 : ℝ) (258816179099/500000000000 : ℝ) (258812099981/500000000000 : ℝ) (51762419997/100000000000 : ℝ) (129407069769/250000000000 : ℝ) (129407069771/250000000000 : ℝ) (517628279059/1000000000000 : ℝ) (129407069767/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 4 (129407069769/250000000000 : ℝ) (129407069771/250000000000 : ℝ) (517628279059/1000000000000 : ℝ) (129407069767/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 5 (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 6 (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4503/32768 : ℝ))) 7 (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4503/32768 : ℝ)) hmem 8 (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4503/32768 : ℝ))) hcmem 8 (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4503/32768 : ℝ)) (495128054191/500000000000 : ℝ) (198051221677/200000000000 : ℝ) (517628279067/1000000000000 : ℝ) (129407069769/250000000000 : ℝ) (821089203609/1000000000000 : ℝ) (821089203627/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0395_exp_lower
  have heNumeric : (2019016583467/1000000000000 : ℝ)/4 ≤ Real.exp (-10938940929907/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016583467/1000000000000 : ℝ)/4 ≤ Real.exp ((9005/65536 : ℝ)-(821089203627/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9005/65536 : ℝ) (4503/32768 : ℝ) (821089203627/1000000000000 : ℝ) (2019016583467/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0396; no trusted numerical premise.
theorem cover7_leaf0396_exp_radius : (124693599548027303/125000000000000000 : ℝ) ≤ Real.exp ((-9007/458752 : ℝ)/8) ∧ Real.exp ((-9007/458752 : ℝ)/8) ≤ (39901951855368737/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9007/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0396_exp_lower : (91808943919898701/100000000000000000 : ℝ) ≤ Real.exp ((-5469469746313/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469469746313/8000000000000 : ℝ)/8) ≤ (918089439198987011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469469746313/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0396_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754191209/250000000000 : ℝ) ≤ 4*Real.exp (4503/32768 : ℝ)*Real.exp (-mu (radius 7 (9007/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754191209/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9007/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0396_exp_radius
  have hrNumeric : (196111556803/200000000000 : ℝ) ≤ Real.exp (-9007/458752 : ℝ) ∧ Real.exp (-9007/458752 : ℝ) ≤ (61284861501/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196111556803/200000000000 : ℝ) ≤ (radius 7 (9007/65536 : ℝ)) ∧ (radius 7 (9007/65536 : ℝ)) ≤ (61284861501/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9007/65536 : ℝ)) (196111556803/200000000000 : ℝ) (61284861501/62500000000 : ℝ) (49057639699/250000000000 : ℝ) (98115279401/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9007/65536 : ℝ)) (196111556803/200000000000 : ℝ) (61284861501/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196111556803/200000000000 : ℝ) (61284861501/62500000000 : ℝ) (990278892007/1000000000000 : ℝ) (123784861501/125000000000 : ℝ) (30944724283/31250000000 : ℝ) (495115588529/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 1 (990278892007/1000000000000 : ℝ) (123784861501/125000000000 : ℝ) (30944724283/31250000000 : ℝ) (495115588529/500000000000 : ℝ) (990255034531/1000000000000 : ℝ) (990255034533/1000000000000 : ℝ) (247563758561/250000000000 : ℝ) (495127517123/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 2 (990255034531/1000000000000 : ℝ) (990255034533/1000000000000 : ℝ) (247563758561/250000000000 : ℝ) (495127517123/500000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 3 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 4 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 5 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 6 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9007/65536 : ℝ)) 7 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9007/65536 : ℝ))) (49057639699/250000000000 : ℝ) (98115279401/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49057639699/250000000000 : ℝ) (98115279401/500000000000 : ℝ) (299057639699/500000000000 : ℝ) (598115279401/1000000000000 : ℝ) (442979185511/1000000000000 : ℝ) (221489592759/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 1 (299057639699/500000000000 : ℝ) (598115279401/1000000000000 : ℝ) (442979185511/1000000000000 : ℝ) (221489592759/500000000000 : ℝ) (260273616227/500000000000 : ℝ) (26027361623/50000000000 : ℝ) (514735484797/1000000000000 : ℝ) (514735484803/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 2 (260273616227/500000000000 : ℝ) (26027361623/50000000000 : ℝ) (514735484797/1000000000000 : ℝ) (514735484803/1000000000000 : ℝ) (4141130869/8000000000 : ℝ) (64705169829/125000000000 : ℝ) (103526640447/200000000000 : ℝ) (258816601121/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 3 (4141130869/8000000000 : ℝ) (64705169829/125000000000 : ℝ) (103526640447/200000000000 : ℝ) (258816601121/500000000000 : ℝ) (51763728043/100000000000 : ℝ) (517637280437/1000000000000 : ℝ) (517637280413/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 4 (51763728043/100000000000 : ℝ) (517637280437/1000000000000 : ℝ) (517637280413/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 5 (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 6 (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9007/65536 : ℝ))) 7 (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9007/65536 : ℝ)) hmem 8 (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9007/65536 : ℝ))) hcmem 8 (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9007/65536 : ℝ)) (990255034387/1000000000000 : ℝ) (99025503439/100000000000 : ℝ) (517637280421/1000000000000 : ℝ) (517637280429/1000000000000 : ℝ) (82110437257/100000000000 : ℝ) (410552186293/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0396_exp_lower
  have heNumeric : (504754191209/250000000000 : ℝ)/4 ≤ Real.exp (-5469469746313/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754191209/250000000000 : ℝ)/4 ≤ Real.exp ((4503/32768 : ℝ)-(410552186293/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4503/32768 : ℝ) (9007/65536 : ℝ) (410552186293/500000000000 : ℝ) (504754191209/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0397; no trusted numerical premise.
theorem cover7_leaf0397_exp_radius : (24938713114344483/25000000000000000 : ℝ) ≤ Real.exp ((-563/28672 : ℝ)/8) ∧ Real.exp ((-563/28672 : ℝ)/8) ≤ (997548524573779321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-563/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0397_exp_lower : (91808944963617927/100000000000000000 : ℝ) ≤ Real.exp ((-10938938037473/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938938037473/16000000000000 : ℝ)/8) ≤ (918089449636179271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938938037473/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0397_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016948459/1000000000000 : ℝ) ≤ 4*Real.exp (9007/65536 : ℝ)*Real.exp (-mu (radius 7 (563/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016948459/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (563/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0397_exp_radius
  have hrNumeric : (980555646571/1000000000000 : ℝ) ≤ Real.exp (-563/28672 : ℝ) ∧ Real.exp (-563/28672 : ℝ) ≤ (245138911643/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980555646571/1000000000000 : ℝ) ≤ (radius 7 (563/4096 : ℝ)) ∧ (radius 7 (563/4096 : ℝ)) ≤ (245138911643/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (563/4096 : ℝ)) (980555646571/1000000000000 : ℝ) (245138911643/250000000000 : ℝ) (196241239233/1000000000000 : ℝ) (196241239239/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (563/4096 : ℝ)) (980555646571/1000000000000 : ℝ) (245138911643/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (563/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980555646571/1000000000000 : ℝ) (245138911643/250000000000 : ℝ) (198055564657/200000000000 : ℝ) (495138911643/500000000000 : ℝ) (99023009779/100000000000 : ℝ) (7736172639/7812500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (563/4096 : ℝ)) 1 (198055564657/200000000000 : ℝ) (495138911643/500000000000 : ℝ) (99023009779/100000000000 : ℝ) (7736172639/7812500000 : ℝ) (990253960537/1000000000000 : ℝ) (990253960539/1000000000000 : ℝ) (990253960249/1000000000000 : ℝ) (247563490063/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (563/4096 : ℝ)) 2 (990253960537/1000000000000 : ℝ) (990253960539/1000000000000 : ℝ) (990253960249/1000000000000 : ℝ) (247563490063/250000000000 : ℝ) (990253960393/1000000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (563/4096 : ℝ)) 3 (990253960393/1000000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (563/4096 : ℝ)) 4 (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (563/4096 : ℝ)) 5 (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (563/4096 : ℝ)) 6 (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (563/4096 : ℝ)) 7 (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (563/4096 : ℝ))) (196241239233/1000000000000 : ℝ) (196241239239/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196241239233/1000000000000 : ℝ) (196241239239/1000000000000 : ℝ) (18691269363/31250000000 : ℝ) (29906030981/50000000000 : ℝ) (221495620291/500000000000 : ℝ) (44299124059/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 1 (18691269363/31250000000 : ℝ) (29906030981/50000000000 : ℝ) (221495620291/500000000000 : ℝ) (44299124059/100000000000 : ℝ) (520555930099/1000000000000 : ℝ) (104111186021/200000000000 : ℝ) (51474478657/100000000000 : ℝ) (514744786577/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 2 (520555930099/1000000000000 : ℝ) (104111186021/200000000000 : ℝ) (51474478657/100000000000 : ℝ) (514744786577/1000000000000 : ℝ) (258825179167/500000000000 : ℝ) (517650358341/1000000000000 : ℝ) (258821101891/500000000000 : ℝ) (517642203789/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 3 (258825179167/500000000000 : ℝ) (517650358341/1000000000000 : ℝ) (258821101891/500000000000 : ℝ) (517642203789/1000000000000 : ℝ) (258823140529/500000000000 : ℝ) (103529256213/200000000000 : ℝ) (517646281041/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 4 (258823140529/500000000000 : ℝ) (103529256213/200000000000 : ℝ) (517646281041/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 5 (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 6 (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (563/4096 : ℝ))) 7 (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (563/4096 : ℝ)) hmem 8 (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (563/4096 : ℝ))) hcmem 8 (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (563/4096 : ℝ)) (123781745049/125000000000 : ℝ) (247563490099/250000000000 : ℝ) (517646281049/1000000000000 : ℝ) (517646281057/1000000000000 : ℝ) (821119540411/1000000000000 : ℝ) (205279885107/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0397_exp_lower
  have heNumeric : (2019016948459/1000000000000 : ℝ)/4 ≤ Real.exp (-10938938037473/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016948459/1000000000000 : ℝ)/4 ≤ Real.exp ((9007/65536 : ℝ)-(205279885107/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9007/65536 : ℝ) (563/4096 : ℝ) (205279885107/250000000000 : ℝ) (2019016948459/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0398; no trusted numerical premise.
theorem cover7_leaf0398_exp_radius : (997548252763414279/1000000000000000000 : ℝ) ≤ Real.exp ((-1287/65536 : ℝ)/8) ∧ Real.exp ((-1287/65536 : ℝ)/8) ≤ (24938706319085357/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1287/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0398_exp_lower : (459044730100952087/500000000000000000 : ℝ) ≤ Real.exp ((-27347341411/40000000000 : ℝ)/8) ∧ Real.exp ((-27347341411/40000000000 : ℝ)/8) ≤ (36723578408076167/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27347341411/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0398_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252377141793/125000000000 : ℝ) ≤ 4*Real.exp (563/4096 : ℝ)*Real.exp (-mu (radius 7 (9009/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (252377141793/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9009/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0398_exp_radius
  have hrNumeric : (980553509131/1000000000000 : ℝ) ≤ Real.exp (-1287/65536 : ℝ) ∧ Real.exp (-1287/65536 : ℝ) ≤ (245138377283/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980553509131/1000000000000 : ℝ) ≤ (radius 7 (9009/65536 : ℝ)) ∧ (radius 7 (9009/65536 : ℝ)) ≤ (245138377283/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9009/65536 : ℝ)) (980553509131/1000000000000 : ℝ) (245138377283/250000000000 : ℝ) (39250383809/200000000000 : ℝ) (196251919051/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9009/65536 : ℝ)) (980553509131/1000000000000 : ℝ) (245138377283/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980553509131/1000000000000 : ℝ) (245138377283/250000000000 : ℝ) (198055350913/200000000000 : ℝ) (495138377283/500000000000 : ℝ) (495114509263/500000000000 : ℝ) (990229018527/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 1 (198055350913/200000000000 : ℝ) (495138377283/500000000000 : ℝ) (495114509263/500000000000 : ℝ) (990229018527/1000000000000 : ℝ) (198050577309/200000000000 : ℝ) (990252886547/1000000000000 : ℝ) (990252886257/1000000000000 : ℝ) (990252886259/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 2 (198050577309/200000000000 : ℝ) (990252886547/1000000000000 : ℝ) (990252886257/1000000000000 : ℝ) (990252886259/1000000000000 : ℝ) (990252886401/1000000000000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 3 (990252886401/1000000000000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 4 (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 5 (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 6 (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9009/65536 : ℝ)) 7 (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9009/65536 : ℝ))) (39250383809/200000000000 : ℝ) (196251919051/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39250383809/200000000000 : ℝ) (196251919051/1000000000000 : ℝ) (299062979761/500000000000 : ℝ) (299062979763/500000000000 : ℝ) (22150164731/50000000000 : ℝ) (110750823657/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 1 (299062979761/500000000000 : ℝ) (299062979763/500000000000 : ℝ) (22150164731/50000000000 : ℝ) (110750823657/250000000000 : ℝ) (520564627071/1000000000000 : ℝ) (520564627077/1000000000000 : ℝ) (257377043783/500000000000 : ℝ) (514754087573/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 2 (520564627071/1000000000000 : ℝ) (520564627077/1000000000000 : ℝ) (257377043783/500000000000 : ℝ) (514754087573/1000000000000 : ℝ) (258829678659/500000000000 : ℝ) (20706374293/40000000000 : ℝ) (517651204603/1000000000000 : ℝ) (51765120461/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 3 (258829678659/500000000000 : ℝ) (20706374293/40000000000 : ℝ) (517651204603/1000000000000 : ℝ) (51765120461/100000000000 : ℝ) (1617672753/3125000000 : ℝ) (64706910121/125000000000 : ℝ) (32353455059/62500000000 : ℝ) (64706910119/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 4 (1617672753/3125000000 : ℝ) (64706910121/125000000000 : ℝ) (32353455059/62500000000 : ℝ) (64706910119/125000000000 : ℝ) (64706910119/125000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 5 (64706910119/125000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 6 (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9009/65536 : ℝ))) 7 (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9009/65536 : ℝ)) hmem 8 (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9009/65536 : ℝ))) hcmem 8 (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9009/65536 : ℝ)) (309454027/312500000 : ℝ) (990252886403/1000000000000 : ℝ) (517655280951/1000000000000 : ℝ) (1617672753/3125000000 : ℝ) (205283676783/250000000000 : ℝ) (16422694143/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0398_exp_lower
  have heNumeric : (252377141793/125000000000 : ℝ)/4 ≤ Real.exp (-27347341411/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252377141793/125000000000 : ℝ)/4 ≤ Real.exp ((563/4096 : ℝ)-(16422694143/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (563/4096 : ℝ) (9009/65536 : ℝ) (16422694143/20000000000 : ℝ) (252377141793/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0399; no trusted numerical premise.
theorem cover7_leaf0399_exp_radius : (997547980953123299/1000000000000000000 : ℝ) ≤ Real.exp ((-4505/229376 : ℝ)/8) ∧ Real.exp ((-4505/229376 : ℝ)/8) ≤ (9975479809531233/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4505/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0399_exp_lower : (459044735448941571/500000000000000000 : ℝ) ≤ Real.exp ((-10938935073167/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938935073167/16000000000000 : ℝ)/8) ≤ (918089470897883143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938935073167/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0399_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019017322521/1000000000000 : ℝ) ≤ 4*Real.exp (9009/65536 : ℝ)*Real.exp (-mu (radius 7 (4505/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019017322521/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4505/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0399_exp_radius
  have hrNumeric : (980551371697/1000000000000 : ℝ) ≤ Real.exp (-4505/229376 : ℝ) ∧ Real.exp (-4505/229376 : ℝ) ≤ (490275685849/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980551371697/1000000000000 : ℝ) ≤ (radius 7 (4505/32768 : ℝ)) ∧ (radius 7 (4505/32768 : ℝ)) ≤ (490275685849/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4505/32768 : ℝ)) (980551371697/1000000000000 : ℝ) (490275685849/500000000000 : ℝ) (98131299111/500000000000 : ℝ) (49065649557/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4505/32768 : ℝ)) (980551371697/1000000000000 : ℝ) (490275685849/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980551371697/1000000000000 : ℝ) (490275685849/500000000000 : ℝ) (123784460731/125000000000 : ℝ) (990275685849/1000000000000 : ℝ) (495113969631/500000000000 : ℝ) (15472311551/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 1 (123784460731/125000000000 : ℝ) (990275685849/1000000000000 : ℝ) (495113969631/500000000000 : ℝ) (15472311551/15625000000 : ℝ) (198050362511/200000000000 : ℝ) (990251812557/1000000000000 : ℝ) (990251812267/1000000000000 : ℝ) (990251812269/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 2 (198050362511/200000000000 : ℝ) (990251812557/1000000000000 : ℝ) (990251812267/1000000000000 : ℝ) (990251812269/1000000000000 : ℝ) (990251812411/1000000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 3 (990251812411/1000000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 4 (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 5 (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 6 (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4505/32768 : ℝ)) 7 (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4505/32768 : ℝ))) (98131299111/500000000000 : ℝ) (49065649557/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98131299111/500000000000 : ℝ) (49065649557/250000000000 : ℝ) (598131299111/1000000000000 : ℝ) (299065649557/500000000000 : ℝ) (221507673807/500000000000 : ℝ) (221507673811/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 1 (598131299111/1000000000000 : ℝ) (299065649557/500000000000 : ℝ) (221507673807/500000000000 : ℝ) (221507673811/500000000000 : ℝ) (260286661681/500000000000 : ℝ) (65071665421/125000000000 : ℝ) (20590535511/40000000000 : ℝ) (257381693891/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 2 (260286661681/500000000000 : ℝ) (65071665421/125000000000 : ℝ) (20590535511/40000000000 : ℝ) (257381693891/500000000000 : ℝ) (32354272223/62500000000 : ℝ) (20706734223/40000000000 : ℝ) (517660204689/1000000000000 : ℝ) (64707525587/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 3 (32354272223/62500000000 : ℝ) (20706734223/40000000000 : ℝ) (517660204689/1000000000000 : ℝ) (64707525587/125000000000 : ℝ) (8088504377/15625000000 : ℝ) (64708035017/125000000000 : ℝ) (32354017507/62500000000 : ℝ) (12941607003/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 4 (8088504377/15625000000 : ℝ) (64708035017/125000000000 : ℝ) (32354017507/62500000000 : ℝ) (12941607003/25000000000 : ℝ) (12941607003/25000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 5 (12941607003/25000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 6 (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4505/32768 : ℝ))) 7 (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4505/32768 : ℝ)) hmem 8 (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4505/32768 : ℝ))) hcmem 8 (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4505/32768 : ℝ)) (99025181241/100000000000 : ℝ) (990251812413/1000000000000 : ℝ) (517664280119/1000000000000 : ℝ) (8088504377/15625000000 : ℝ) (10264373409/12500000000 : ℝ) (821149872737/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0399_exp_lower
  have heNumeric : (2019017322521/1000000000000 : ℝ)/4 ≤ Real.exp (-10938935073167/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019017322521/1000000000000 : ℝ)/4 ≤ Real.exp ((9009/65536 : ℝ)-(821149872737/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9009/65536 : ℝ) (4505/32768 : ℝ) (821149872737/1000000000000 : ℝ) (2019017322521/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0375_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0375_certificate
#check SmaleRate.Proofs.cover7_leaf0376_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0376_certificate
#check SmaleRate.Proofs.cover7_leaf0377_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0377_certificate
#check SmaleRate.Proofs.cover7_leaf0378_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0378_certificate
#check SmaleRate.Proofs.cover7_leaf0379_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0379_certificate
#check SmaleRate.Proofs.cover7_leaf0380_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0380_certificate
#check SmaleRate.Proofs.cover7_leaf0381_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0381_certificate
#check SmaleRate.Proofs.cover7_leaf0382_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0382_certificate
#check SmaleRate.Proofs.cover7_leaf0383_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0383_certificate
#check SmaleRate.Proofs.cover7_leaf0384_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0384_certificate
#check SmaleRate.Proofs.cover7_leaf0385_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0385_certificate
#check SmaleRate.Proofs.cover7_leaf0386_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0386_certificate
#check SmaleRate.Proofs.cover7_leaf0387_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0387_certificate
#check SmaleRate.Proofs.cover7_leaf0388_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0388_certificate
#check SmaleRate.Proofs.cover7_leaf0389_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0389_certificate
#check SmaleRate.Proofs.cover7_leaf0390_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0390_certificate
#check SmaleRate.Proofs.cover7_leaf0391_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0391_certificate
#check SmaleRate.Proofs.cover7_leaf0392_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0392_certificate
#check SmaleRate.Proofs.cover7_leaf0393_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0393_certificate
#check SmaleRate.Proofs.cover7_leaf0394_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0394_certificate
#check SmaleRate.Proofs.cover7_leaf0395_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0395_certificate
#check SmaleRate.Proofs.cover7_leaf0396_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0396_certificate
#check SmaleRate.Proofs.cover7_leaf0397_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0397_certificate
#check SmaleRate.Proofs.cover7_leaf0398_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0398_certificate
#check SmaleRate.Proofs.cover7_leaf0399_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0399_certificate
