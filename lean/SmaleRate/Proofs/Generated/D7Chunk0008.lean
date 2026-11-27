/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0200; no trusted numerical premise.
theorem cover7_leaf0200_exp_radius : (249400518165039583/250000000000000000 : ℝ) ≤ Real.exp ((-8811/458752 : ℝ)/8) ∧ Real.exp ((-8811/458752 : ℝ)/8) ≤ (997602072660158333/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8811/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0200_exp_lower : (918089915060101217/1000000000000000000 : ℝ) ≤ Real.exp ((-5469436574051/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469436574051/8000000000000 : ℝ)/8) ≤ (459044957530050609/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469436574051/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0200_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504756284193/250000000000 : ℝ) ≤ 4*Real.exp (4405/32768 : ℝ)*Real.exp (-mu (radius 7 (8811/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504756284193/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8811/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0200_exp_radius
  have hrNumeric : (196195362601/200000000000 : ℝ) ≤ Real.exp (-8811/458752 : ℝ) ∧ Real.exp (-8811/458752 : ℝ) ≤ (490488406503/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196195362601/200000000000 : ℝ) ≤ (radius 7 (8811/65536 : ℝ)) ∧ (radius 7 (8811/65536 : ℝ)) ≤ (490488406503/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8811/65536 : ℝ)) (196195362601/200000000000 : ℝ) (490488406503/500000000000 : ℝ) (194124940037/1000000000000 : ℝ) (194124940043/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8811/65536 : ℝ)) (196195362601/200000000000 : ℝ) (490488406503/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196195362601/200000000000 : ℝ) (490488406503/500000000000 : ℝ) (495244203251/500000000000 : ℝ) (990488406503/1000000000000 : ℝ) (990442735853/1000000000000 : ℝ) (198088547171/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 1 (495244203251/500000000000 : ℝ) (990488406503/1000000000000 : ℝ) (990442735853/1000000000000 : ℝ) (198088547171/200000000000 : ℝ) (990465571177/1000000000000 : ℝ) (990465571179/1000000000000 : ℝ) (495232785457/500000000000 : ℝ) (247616392729/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 2 (990465571177/1000000000000 : ℝ) (990465571179/1000000000000 : ℝ) (495232785457/500000000000 : ℝ) (247616392729/250000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 3 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 4 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 5 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 6 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8811/65536 : ℝ)) 7 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8811/65536 : ℝ))) (194124940037/1000000000000 : ℝ) (194124940043/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194124940037/1000000000000 : ℝ) (194124940043/1000000000000 : ℝ) (298531235009/500000000000 : ℝ) (298531235011/500000000000 : ℝ) (440596118953/1000000000000 : ℝ) (440596118961/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 1 (298531235009/500000000000 : ℝ) (298531235011/500000000000 : ℝ) (440596118953/1000000000000 : ℝ) (440596118961/1000000000000 : ℝ) (103765858897/200000000000 : ℝ) (129707323623/250000000000 : ℝ) (512897072581/1000000000000 : ℝ) (128224268147/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 2 (103765858897/200000000000 : ℝ) (129707323623/250000000000 : ℝ) (512897072581/1000000000000 : ℝ) (128224268147/250000000000 : ℝ) (515863183533/1000000000000 : ℝ) (25793159177/50000000000 : ℝ) (515854656187/1000000000000 : ℝ) (103170931239/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 3 (515863183533/1000000000000 : ℝ) (25793159177/50000000000 : ℝ) (515854656187/1000000000000 : ℝ) (103170931239/200000000000 : ℝ) (25792945993/50000000000 : ℝ) (128964729967/250000000000 : ℝ) (257929459921/500000000000 : ℝ) (10317178397/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 4 (25792945993/50000000000 : ℝ) (128964729967/250000000000 : ℝ) (257929459921/500000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919851/1000000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 5 (515858919851/1000000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 6 (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8811/65536 : ℝ))) 7 (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8811/65536 : ℝ)) hmem 8 (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8811/65536 : ℝ))) hcmem 8 (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8811/65536 : ℝ)) (198093114209/200000000000 : ℝ) (123808196381/125000000000 : ℝ) (10317178397/20000000000 : ℝ) (515858919859/1000000000000 : ℝ) (818109503379/1000000000000 : ℝ) (818109503397/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0200_exp_lower
  have heNumeric : (504756284193/250000000000 : ℝ)/4 ≤ Real.exp (-5469436574051/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504756284193/250000000000 : ℝ)/4 ≤ Real.exp ((4405/32768 : ℝ)-(818109503397/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4405/32768 : ℝ) (8811/65536 : ℝ) (818109503397/1000000000000 : ℝ) (504756284193/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0201; no trusted numerical premise.
theorem cover7_leaf0201_exp_radius : (997601800835202597/1000000000000000000 : ℝ) ≤ Real.exp ((-2203/114688 : ℝ)/8) ∧ Real.exp ((-2203/114688 : ℝ)/8) ≤ (498800900417601299/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2203/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0201_exp_lower : (459044949866700357/500000000000000000 : ℝ) ≤ Real.exp ((-10938875284949/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938875284949/16000000000000 : ℝ)/8) ≤ (183617979946680143/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938875284949/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0201_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512433563/500000000000 : ℝ) ≤ 4*Real.exp (8811/65536 : ℝ)*Real.exp (-mu (radius 7 (2203/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512433563/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2203/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0201_exp_radius
  have hrNumeric : (122621834331/125000000000 : ℝ) ≤ Real.exp (-2203/114688 : ℝ) ∧ Real.exp (-2203/114688 : ℝ) ≤ (980974674649/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122621834331/125000000000 : ℝ) ≤ (radius 7 (2203/16384 : ℝ)) ∧ (radius 7 (2203/16384 : ℝ)) ≤ (980974674649/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2203/16384 : ℝ)) (122621834331/125000000000 : ℝ) (980974674649/1000000000000 : ℝ) (97067872771/500000000000 : ℝ) (48533936387/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2203/16384 : ℝ)) (122621834331/125000000000 : ℝ) (980974674649/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122621834331/125000000000 : ℝ) (980974674649/1000000000000 : ℝ) (247621834331/250000000000 : ℝ) (39619493493/40000000000 : ℝ) (990441656357/1000000000000 : ℝ) (495220828179/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 1 (247621834331/250000000000 : ℝ) (39619493493/40000000000 : ℝ) (990441656357/1000000000000 : ℝ) (495220828179/500000000000 : ℝ) (24761612421/25000000000 : ℝ) (495232248421/500000000000 : ℝ) (990464496577/1000000000000 : ℝ) (990464496579/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 2 (24761612421/25000000000 : ℝ) (495232248421/500000000000 : ℝ) (990464496577/1000000000000 : ℝ) (990464496579/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 3 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 4 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 5 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 6 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2203/16384 : ℝ)) 7 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2203/16384 : ℝ))) (97067872771/500000000000 : ℝ) (48533936387/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97067872771/500000000000 : ℝ) (48533936387/250000000000 : ℝ) (597067872771/1000000000000 : ℝ) (298533936387/500000000000 : ℝ) (13769011911/31250000000 : ℝ) (11015209529/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 1 (597067872771/1000000000000 : ℝ) (298533936387/500000000000 : ℝ) (13769011911/31250000000 : ℝ) (11015209529/25000000000 : ℝ) (518838126961/1000000000000 : ℝ) (518838126967/1000000000000 : ℝ) (256453265167/500000000000 : ℝ) (512906530341/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 2 (518838126961/1000000000000 : ℝ) (518838126967/1000000000000 : ℝ) (256453265167/500000000000 : ℝ) (512906530341/1000000000000 : ℝ) (515872328647/1000000000000 : ℝ) (257936164327/500000000000 : ℝ) (2063455213/4000000000 : ℝ) (257931901629/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 3 (515872328647/1000000000000 : ℝ) (257936164327/500000000000 : ℝ) (2063455213/4000000000 : ℝ) (257931901629/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (128967016489/250000000000 : ℝ) (51586806593/100000000000 : ℝ) (515868065939/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 4 (128967016487/250000000000 : ℝ) (128967016489/250000000000 : ℝ) (51586806593/100000000000 : ℝ) (515868065939/1000000000000 : ℝ) (515868065939/1000000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 5 (515868065939/1000000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 6 (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2203/16384 : ℝ))) 7 (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2203/16384 : ℝ)) hmem 8 (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2203/16384 : ℝ))) hcmem 8 (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2203/16384 : ℝ)) (247616124177/250000000000 : ℝ) (990464496711/1000000000000 : ℝ) (257934032969/500000000000 : ℝ) (128967016487/250000000000 : ℝ) (20453122393/25000000000 : ℝ) (818124895739/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0201_exp_lower
  have heNumeric : (1009512433563/500000000000 : ℝ)/4 ≤ Real.exp (-10938875284949/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512433563/500000000000 : ℝ)/4 ≤ Real.exp ((8811/65536 : ℝ)-(818124895739/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8811/65536 : ℝ) (2203/16384 : ℝ) (818124895739/1000000000000 : ℝ) (1009512433563/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0202; no trusted numerical premise.
theorem cover7_leaf0202_exp_radius : (31175047781572529/31250000000000000 : ℝ) ≤ Real.exp ((-1259/65536 : ℝ)/8) ∧ Real.exp ((-1259/65536 : ℝ)/8) ≤ (997601529010320929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1259/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0202_exp_lower : (114761235567520973/125000000000000000 : ℝ) ≤ Real.exp ((-2734719350797/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734719350797/4000000000000 : ℝ)/8) ≤ (183617976908033557/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734719350797/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0202_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024599827/1000000000000 : ℝ) ≤ 4*Real.exp (2203/16384 : ℝ)*Real.exp (-mu (radius 7 (8813/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024599827/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8813/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0202_exp_radius
  have hrNumeric : (196194507259/200000000000 : ℝ) ≤ Real.exp (-1259/65536 : ℝ) ∧ Real.exp (-1259/65536 : ℝ) ≤ (122621567037/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196194507259/200000000000 : ℝ) ≤ (radius 7 (8813/65536 : ℝ)) ∧ (radius 7 (8813/65536 : ℝ)) ≤ (122621567037/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8813/65536 : ℝ)) (196194507259/200000000000 : ℝ) (122621567037/125000000000 : ℝ) (194146550401/1000000000000 : ℝ) (24268318801/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8813/65536 : ℝ)) (196194507259/200000000000 : ℝ) (122621567037/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196194507259/200000000000 : ℝ) (122621567037/125000000000 : ℝ) (990486268147/1000000000000 : ℝ) (247621567037/250000000000 : ℝ) (495220288431/500000000000 : ℝ) (990440576863/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 1 (990486268147/1000000000000 : ℝ) (247621567037/250000000000 : ℝ) (495220288431/500000000000 : ℝ) (990440576863/1000000000000 : ℝ) (123807927813/125000000000 : ℝ) (495231711253/500000000000 : ℝ) (990463422241/1000000000000 : ℝ) (990463422243/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 2 (123807927813/125000000000 : ℝ) (495231711253/500000000000 : ℝ) (990463422241/1000000000000 : ℝ) (990463422243/1000000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 3 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 4 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 5 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 6 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8813/65536 : ℝ)) 7 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8813/65536 : ℝ))) (194146550401/1000000000000 : ℝ) (24268318801/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194146550401/1000000000000 : ℝ) (24268318801/125000000000 : ℝ) (373170797/625000000 : ℝ) (149268318801/250000000000 : ℝ) (440620642277/1000000000000 : ℝ) (220310321143/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 1 (373170797/625000000 : ℝ) (149268318801/250000000000 : ℝ) (440620642277/1000000000000 : ℝ) (220310321143/500000000000 : ℝ) (259423479369/500000000000 : ℝ) (103769391749/200000000000 : ℝ) (512915987277/1000000000000 : ℝ) (102583197457/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 2 (259423479369/500000000000 : ℝ) (103769391749/200000000000 : ℝ) (512915987277/1000000000000 : ℝ) (102583197457/200000000000 : ℝ) (515881473007/1000000000000 : ℝ) (103176294603/200000000000 : ℝ) (515872949559/1000000000000 : ℝ) (515872949567/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 3 (515881473007/1000000000000 : ℝ) (103176294603/200000000000 : ℝ) (515872949559/1000000000000 : ℝ) (515872949567/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211291/1000000000000 : ℝ) (103175442253/200000000000 : ℝ) (257938605637/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 4 (515877211283/1000000000000 : ℝ) (515877211291/1000000000000 : ℝ) (103175442253/200000000000 : ℝ) (257938605637/500000000000 : ℝ) (257938605637/500000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 5 (257938605637/500000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 6 (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8813/65536 : ℝ))) 7 (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8813/65536 : ℝ)) hmem 8 (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8813/65536 : ℝ))) hcmem 8 (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8813/65536 : ℝ)) (247615855593/250000000000 : ℝ) (7923707379/8000000000 : ℝ) (515877211273/1000000000000 : ℝ) (515877211283/1000000000000 : ℝ) (409070143449/500000000000 : ℝ) (409070143459/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0202_exp_lower
  have heNumeric : (2019024599827/1000000000000 : ℝ)/4 ≤ Real.exp (-2734719350797/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024599827/1000000000000 : ℝ)/4 ≤ Real.exp ((2203/16384 : ℝ)-(409070143459/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2203/16384 : ℝ) (8813/65536 : ℝ) (409070143459/500000000000 : ℝ) (2019024599827/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0203; no trusted numerical premise.
theorem cover7_leaf0203_exp_radius : (39904050287420533/40000000000000000 : ℝ) ≤ Real.exp ((-4407/229376 : ℝ)/8) ∧ Real.exp ((-4407/229376 : ℝ)/8) ≤ (498800628592756663/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4407/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0203_exp_lower : (918089869481205749/1000000000000000000 : ℝ) ≤ Real.exp ((-10938879502707/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938879502707/16000000000000 : ℝ)/8) ≤ (3672359477924823/4000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938879502707/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0203_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024334891/1000000000000 : ℝ) ≤ 4*Real.exp (8813/65536 : ℝ)*Real.exp (-mu (radius 7 (4407/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024334891/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4407/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0203_exp_radius
  have hrNumeric : (980970397947/1000000000000 : ℝ) ≤ Real.exp (-4407/229376 : ℝ) ∧ Real.exp (-4407/229376 : ℝ) ≤ (245242599487/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980970397947/1000000000000 : ℝ) ≤ (radius 7 (4407/32768 : ℝ)) ∧ (radius 7 (4407/32768 : ℝ)) ≤ (245242599487/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4407/32768 : ℝ)) (980970397947/1000000000000 : ℝ) (245242599487/250000000000 : ℝ) (194157354611/1000000000000 : ℝ) (194157354617/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4407/32768 : ℝ)) (980970397947/1000000000000 : ℝ) (245242599487/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980970397947/1000000000000 : ℝ) (245242599487/250000000000 : ℝ) (990485198973/1000000000000 : ℝ) (495242599487/500000000000 : ℝ) (123804937171/125000000000 : ℝ) (990439497369/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 1 (990485198973/1000000000000 : ℝ) (495242599487/500000000000 : ℝ) (123804937171/125000000000 : ℝ) (990439497369/1000000000000 : ℝ) (99046234817/100000000000 : ℝ) (247615587043/250000000000 : ℝ) (495231173953/500000000000 : ℝ) (247615586977/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 2 (99046234817/100000000000 : ℝ) (247615587043/250000000000 : ℝ) (495231173953/500000000000 : ℝ) (247615586977/250000000000 : ℝ) (495231174019/500000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 3 (495231174019/500000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 4 (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 5 (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 6 (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4407/32768 : ℝ)) 7 (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4407/32768 : ℝ))) (194157354611/1000000000000 : ℝ) (194157354617/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194157354611/1000000000000 : ℝ) (194157354617/1000000000000 : ℝ) (119415735461/200000000000 : ℝ) (597078677309/1000000000000 : ℝ) (110158225581/250000000000 : ℝ) (110158225583/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 1 (119415735461/200000000000 : ℝ) (597078677309/1000000000000 : ℝ) (110158225581/250000000000 : ℝ) (110158225583/250000000000 : ℝ) (259427894907/500000000000 : ℝ) (518855789821/1000000000000 : ℝ) (512925443409/1000000000000 : ℝ) (64115680427/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 2 (259427894907/500000000000 : ℝ) (518855789821/1000000000000 : ℝ) (512925443409/1000000000000 : ℝ) (64115680427/125000000000 : ℝ) (515890616611/1000000000000 : ℝ) (515890616619/1000000000000 : ℝ) (51588209511/100000000000 : ℝ) (257941047559/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 3 (515890616611/1000000000000 : ℝ) (515890616619/1000000000000 : ℝ) (51588209511/100000000000 : ℝ) (257941047559/500000000000 : ℝ) (25794317793/50000000000 : ℝ) (515886355869/1000000000000 : ℝ) (257943177921/500000000000 : ℝ) (515886355851/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 4 (25794317793/50000000000 : ℝ) (515886355869/1000000000000 : ℝ) (257943177921/500000000000 : ℝ) (515886355851/1000000000000 : ℝ) (515886355851/1000000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 5 (515886355851/1000000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 6 (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4407/32768 : ℝ))) 7 (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4407/32768 : ℝ)) hmem 8 (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4407/32768 : ℝ))) hcmem 8 (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4407/32768 : ℝ)) (990462348037/1000000000000 : ℝ) (24761558701/25000000000 : ℝ) (10317727117/20000000000 : ℝ) (25794317793/50000000000 : ℝ) (204538919227/250000000000 : ℝ) (818155676927/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0203_exp_lower
  have heNumeric : (2019024334891/1000000000000 : ℝ)/4 ≤ Real.exp (-10938879502707/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024334891/1000000000000 : ℝ)/4 ≤ Real.exp ((8813/65536 : ℝ)-(818155676927/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8813/65536 : ℝ) (4407/32768 : ℝ) (818155676927/1000000000000 : ℝ) (2019024334891/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0204; no trusted numerical premise.
theorem cover7_leaf0204_exp_radius : (997600985360779789/1000000000000000000 : ℝ) ≤ Real.exp ((-8815/458752 : ℝ)/8) ∧ Real.exp ((-8815/458752 : ℝ)/8) ≤ (99760098536077979/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8815/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0204_exp_lower : (918089854556399841/1000000000000000000 : ℝ) ≤ Real.exp ((-5469440791761/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469440791761/8000000000000 : ℝ)/8) ≤ (459044927278199921/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469440791761/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0204_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403804814463/200000000000 : ℝ) ≤ 4*Real.exp (4407/32768 : ℝ)*Real.exp (-mu (radius 7 (8815/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403804814463/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8815/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0204_exp_radius
  have hrNumeric : (245242064901/250000000000 : ℝ) ≤ Real.exp (-8815/458752 : ℝ) ∧ Real.exp (-8815/458752 : ℝ) ≤ (196193651921/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245242064901/250000000000 : ℝ) ≤ (radius 7 (8815/65536 : ℝ)) ∧ (radius 7 (8815/65536 : ℝ)) ≤ (196193651921/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8815/65536 : ℝ)) (245242064901/250000000000 : ℝ) (196193651921/200000000000 : ℝ) (194168158171/1000000000000 : ℝ) (194168158177/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8815/65536 : ℝ)) (245242064901/250000000000 : ℝ) (196193651921/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245242064901/250000000000 : ℝ) (196193651921/200000000000 : ℝ) (495242064901/500000000000 : ℝ) (990484129803/1000000000000 : ℝ) (7923507343/8000000000 : ℝ) (990438417877/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 1 (495242064901/500000000000 : ℝ) (990484129803/1000000000000 : ℝ) (7923507343/8000000000 : ℝ) (990438417877/1000000000000 : ℝ) (495230636919/500000000000 : ℝ) (12380765923/12500000000 : ℝ) (495230636787/500000000000 : ℝ) (990461273577/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 2 (495230636919/500000000000 : ℝ) (12380765923/12500000000 : ℝ) (495230636787/500000000000 : ℝ) (990461273577/1000000000000 : ℝ) (495230636853/500000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 3 (495230636853/500000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 4 (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 5 (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 6 (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8815/65536 : ℝ)) 7 (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8815/65536 : ℝ))) (194168158171/1000000000000 : ℝ) (194168158177/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194168158171/1000000000000 : ℝ) (194168158177/1000000000000 : ℝ) (119416815817/200000000000 : ℝ) (597084079089/1000000000000 : ℝ) (440645161293/1000000000000 : ℝ) (4406451613/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 1 (119416815817/200000000000 : ℝ) (597084079089/1000000000000 : ℝ) (440645161293/1000000000000 : ℝ) (4406451613/10000000000 : ℝ) (518864620189/1000000000000 : ℝ) (103772924039/200000000000 : ℝ) (64116862341/125000000000 : ℝ) (102586979747/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 2 (518864620189/1000000000000 : ℝ) (103772924039/200000000000 : ℝ) (64116862341/125000000000 : ℝ) (102586979747/200000000000 : ℝ) (257949879729/500000000000 : ℝ) (103179951893/200000000000 : ℝ) (16121601247/31250000000 : ℝ) (515891239911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 3 (257949879729/500000000000 : ℝ) (103179951893/200000000000 : ℝ) (16121601247/31250000000 : ℝ) (515891239911/1000000000000 : ℝ) (515895499681/1000000000000 : ℝ) (64486937461/125000000000 : ℝ) (515895499663/1000000000000 : ℝ) (515895499671/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 4 (515895499681/1000000000000 : ℝ) (64486937461/125000000000 : ℝ) (515895499663/1000000000000 : ℝ) (515895499671/1000000000000 : ℝ) (64486937459/125000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 5 (64486937459/125000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 6 (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8815/65536 : ℝ))) 7 (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8815/65536 : ℝ)) hmem 8 (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8815/65536 : ℝ))) hcmem 8 (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8815/65536 : ℝ)) (198092254741/200000000000 : ℝ) (990461273709/1000000000000 : ℝ) (515895499671/1000000000000 : ℝ) (3224346873/6250000000 : ℝ) (204542766437/250000000000 : ℝ) (818171065767/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0204_exp_lower
  have heNumeric : (403804814463/200000000000 : ℝ)/4 ≤ Real.exp (-5469440791761/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403804814463/200000000000 : ℝ)/4 ≤ Real.exp ((4407/32768 : ℝ)-(818171065767/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4407/32768 : ℝ) (8815/65536 : ℝ) (818171065767/1000000000000 : ℝ) (403804814463/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0205; no trusted numerical premise.
theorem cover7_leaf0205_exp_radius : (389687778725047/390625000000000 : ℝ) ≤ Real.exp ((-551/28672 : ℝ)/8) ∧ Real.exp ((-551/28672 : ℝ)/8) ≤ (997600713536120321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-551/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0205_exp_lower : (918089839765176247/1000000000000000000 : ℝ) ≤ Real.exp ((-10938883645713/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938883645713/16000000000000 : ℝ)/8) ≤ (114761229970647031/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938883645713/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0205_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023812089/1000000000000 : ℝ) ≤ 4*Real.exp (8815/65536 : ℝ)*Real.exp (-mu (radius 7 (551/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023812089/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (551/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0205_exp_radius
  have hrNumeric : (196193224253/200000000000 : ℝ) ≤ Real.exp (-551/28672 : ℝ) ∧ Real.exp (-551/28672 : ℝ) ≤ (490483060633/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196193224253/200000000000 : ℝ) ≤ (radius 7 (551/4096 : ℝ)) ∧ (radius 7 (551/4096 : ℝ)) ≤ (490483060633/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (551/4096 : ℝ)) (196193224253/200000000000 : ℝ) (490483060633/500000000000 : ℝ) (38835792217/200000000000 : ℝ) (194178961091/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (551/4096 : ℝ)) (196193224253/200000000000 : ℝ) (490483060633/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (551/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196193224253/200000000000 : ℝ) (490483060633/500000000000 : ℝ) (123810382579/125000000000 : ℝ) (990483060633/1000000000000 : ℝ) (990437338383/1000000000000 : ℝ) (198087467677/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (551/4096 : ℝ)) 1 (123810382579/125000000000 : ℝ) (990483060633/1000000000000 : ℝ) (990437338383/1000000000000 : ℝ) (198087467677/200000000000 : ℝ) (990460199507/1000000000000 : ℝ) (990460199509/1000000000000 : ℝ) (990460199243/1000000000000 : ℝ) (495230099623/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (551/4096 : ℝ)) 2 (990460199507/1000000000000 : ℝ) (990460199509/1000000000000 : ℝ) (990460199243/1000000000000 : ℝ) (495230099623/500000000000 : ℝ) (1584736319/1600000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (551/4096 : ℝ)) 3 (1584736319/1600000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (551/4096 : ℝ)) 4 (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (551/4096 : ℝ)) 5 (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (551/4096 : ℝ)) 6 (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (551/4096 : ℝ)) 7 (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (551/4096 : ℝ))) (38835792217/200000000000 : ℝ) (194178961091/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38835792217/200000000000 : ℝ) (194178961091/1000000000000 : ℝ) (298544740271/500000000000 : ℝ) (298544740273/500000000000 : ℝ) (440657419187/1000000000000 : ℝ) (88131483839/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 1 (298544740271/500000000000 : ℝ) (298544740273/500000000000 : ℝ) (440657419187/1000000000000 : ℝ) (88131483839/200000000000 : ℝ) (64859181233/125000000000 : ℝ) (518873449871/1000000000000 : ℝ) (256472176619/500000000000 : ℝ) (102588870649/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 2 (64859181233/125000000000 : ℝ) (518873449871/1000000000000 : ℝ) (256472176619/500000000000 : ℝ) (102588870649/200000000000 : ℝ) (515908901551/1000000000000 : ℝ) (257954450779/500000000000 : ℝ) (515900383943/1000000000000 : ℝ) (515900383951/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 3 (515908901551/1000000000000 : ℝ) (257954450779/500000000000 : ℝ) (515900383943/1000000000000 : ℝ) (515900383951/1000000000000 : ℝ) (515904642747/1000000000000 : ℝ) (103180928551/200000000000 : ℝ) (515904642729/1000000000000 : ℝ) (515904642737/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 4 (515904642747/1000000000000 : ℝ) (103180928551/200000000000 : ℝ) (515904642729/1000000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321369/500000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 5 (257952321369/500000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 6 (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (551/4096 : ℝ))) 7 (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (551/4096 : ℝ)) hmem 8 (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (551/4096 : ℝ))) hcmem 8 (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (551/4096 : ℝ)) (495230099687/500000000000 : ℝ) (495230099689/500000000000 : ℝ) (515904642737/1000000000000 : ℝ) (257952321373/500000000000 : ℝ) (32727458137/40000000000 : ℝ) (818186453443/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0205_exp_lower
  have heNumeric : (2019023812089/1000000000000 : ℝ)/4 ≤ Real.exp (-10938883645713/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023812089/1000000000000 : ℝ)/4 ≤ Real.exp ((8815/65536 : ℝ)-(818186453443/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8815/65536 : ℝ) (551/4096 : ℝ) (818186453443/1000000000000 : ℝ) (2019023812089/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0206; no trusted numerical premise.
theorem cover7_leaf0206_exp_radius : (249400110427883729/250000000000000000 : ℝ) ≤ Real.exp ((-8817/458752 : ℝ)/8) ∧ Real.exp ((-8817/458752 : ℝ)/8) ≤ (997600441711534917/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8817/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0206_exp_lower : (459044912553997003/500000000000000000 : ℝ) ≤ Real.exp ((-85460044447/125000000000 : ℝ)/8) ∧ Real.exp ((-85460044447/125000000000 : ℝ)/8) ≤ (918089825107994007/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85460044447/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0206_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023554221/1000000000000 : ℝ) ≤ 4*Real.exp (551/4096 : ℝ)*Real.exp (-mu (radius 7 (8817/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023554221/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8817/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0206_exp_radius
  have hrNumeric : (980963982931/1000000000000 : ℝ) ≤ Real.exp (-8817/458752 : ℝ) ∧ Real.exp (-8817/458752 : ℝ) ≤ (245240995733/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980963982931/1000000000000 : ℝ) ≤ (radius 7 (8817/65536 : ℝ)) ∧ (radius 7 (8817/65536 : ℝ)) ≤ (245240995733/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8817/65536 : ℝ)) (980963982931/1000000000000 : ℝ) (245240995733/250000000000 : ℝ) (3883795267/20000000000 : ℝ) (48547440839/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8817/65536 : ℝ)) (980963982931/1000000000000 : ℝ) (245240995733/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980963982931/1000000000000 : ℝ) (245240995733/250000000000 : ℝ) (198096398293/200000000000 : ℝ) (495240995733/500000000000 : ℝ) (990436258893/1000000000000 : ℝ) (198087251779/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 1 (198096398293/200000000000 : ℝ) (495240995733/500000000000 : ℝ) (990436258893/1000000000000 : ℝ) (198087251779/200000000000 : ℝ) (990459125179/1000000000000 : ℝ) (990459125181/1000000000000 : ℝ) (198091824983/200000000000 : ℝ) (990459124917/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 2 (990459125179/1000000000000 : ℝ) (990459125181/1000000000000 : ℝ) (198091824983/200000000000 : ℝ) (990459124917/1000000000000 : ℝ) (990459125047/1000000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 3 (990459125047/1000000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 4 (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 5 (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 6 (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8817/65536 : ℝ)) 7 (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8817/65536 : ℝ))) (3883795267/20000000000 : ℝ) (48547440839/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3883795267/20000000000 : ℝ) (48547440839/250000000000 : ℝ) (23883795267/40000000000 : ℝ) (298547440839/500000000000 : ℝ) (110167419001/250000000000 : ℝ) (110167419003/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 1 (23883795267/40000000000 : ℝ) (298547440839/500000000000 : ℝ) (110167419001/250000000000 : ℝ) (110167419003/250000000000 : ℝ) (518882278839/1000000000000 : ℝ) (103776455769/200000000000 : ℝ) (512953806937/1000000000000 : ℝ) (16029806467/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 2 (518882278839/1000000000000 : ℝ) (103776455769/200000000000 : ℝ) (512953806937/1000000000000 : ℝ) (16029806467/31250000000 : ℝ) (64489755361/125000000000 : ℝ) (103183608579/200000000000 : ℝ) (257954763613/500000000000 : ℝ) (515909527233/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 3 (64489755361/125000000000 : ℝ) (103183608579/200000000000 : ℝ) (257954763613/500000000000 : ℝ) (515909527233/1000000000000 : ℝ) (515913785057/1000000000000 : ℝ) (64489223133/125000000000 : ℝ) (515913785039/1000000000000 : ℝ) (515913785047/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 4 (515913785057/1000000000000 : ℝ) (64489223133/125000000000 : ℝ) (515913785039/1000000000000 : ℝ) (515913785047/1000000000000 : ℝ) (64489223131/125000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 5 (64489223131/125000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 6 (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8817/65536 : ℝ))) 7 (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8817/65536 : ℝ)) hmem 8 (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8817/65536 : ℝ))) hcmem 8 (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8817/65536 : ℝ)) (495229562523/500000000000 : ℝ) (990459125049/1000000000000 : ℝ) (515913785047/1000000000000 : ℝ) (16122305783/31250000000 : ℝ) (409100919967/500000000000 : ℝ) (818201839951/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0206_exp_lower
  have heNumeric : (2019023554221/1000000000000 : ℝ)/4 ≤ Real.exp (-85460044447/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023554221/1000000000000 : ℝ)/4 ≤ Real.exp ((551/4096 : ℝ)-(818201839951/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (551/4096 : ℝ) (8817/65536 : ℝ) (818201839951/1000000000000 : ℝ) (2019023554221/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0207; no trusted numerical premise.
theorem cover7_leaf0207_exp_radius : (997600169887023579/1000000000000000000 : ℝ) ≤ Real.exp ((-4409/229376 : ℝ)/8) ∧ Real.exp ((-4409/229376 : ℝ)/8) ≤ (49880008494351179/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4409/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0207_exp_lower : (459044905291967511/500000000000000000 : ℝ) ≤ Real.exp ((-10938887714159/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938887714159/16000000000000 : ℝ)/8) ≤ (918089810583935023/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938887714159/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0207_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252377912337/125000000000 : ℝ) ≤ 4*Real.exp (8817/65536 : ℝ)*Real.exp (-mu (radius 7 (4409/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252377912337/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4409/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0207_exp_radius
  have hrNumeric : (980961844601/1000000000000 : ℝ) ≤ Real.exp (-4409/229376 : ℝ) ∧ Real.exp (-4409/229376 : ℝ) ≤ (490480922301/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980961844601/1000000000000 : ℝ) ≤ (radius 7 (4409/32768 : ℝ)) ∧ (radius 7 (4409/32768 : ℝ)) ≤ (490480922301/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4409/32768 : ℝ)) (980961844601/1000000000000 : ℝ) (490480922301/500000000000 : ℝ) (19420056497/100000000000 : ℝ) (194200564977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4409/32768 : ℝ)) (980961844601/1000000000000 : ℝ) (490480922301/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980961844601/1000000000000 : ℝ) (490480922301/500000000000 : ℝ) (9904809223/10000000000 : ℝ) (990480922301/1000000000000 : ℝ) (990435179403/1000000000000 : ℝ) (198087035881/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 1 (9904809223/10000000000 : ℝ) (990480922301/1000000000000 : ℝ) (990435179403/1000000000000 : ℝ) (198087035881/200000000000 : ℝ) (990458050851/1000000000000 : ℝ) (990458050853/1000000000000 : ℝ) (990458050587/1000000000000 : ℝ) (990458050589/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 2 (990458050851/1000000000000 : ℝ) (990458050853/1000000000000 : ℝ) (990458050587/1000000000000 : ℝ) (990458050589/1000000000000 : ℝ) (990458050719/1000000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 3 (990458050719/1000000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 4 (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 5 (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 6 (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4409/32768 : ℝ)) 7 (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4409/32768 : ℝ))) (19420056497/100000000000 : ℝ) (194200564977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19420056497/100000000000 : ℝ) (194200564977/1000000000000 : ℝ) (119420056497/200000000000 : ℝ) (597100282489/1000000000000 : ℝ) (110170482937/250000000000 : ℝ) (440681931757/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 1 (119420056497/200000000000 : ℝ) (597100282489/1000000000000 : ℝ) (110170482937/250000000000 : ℝ) (440681931757/1000000000000 : ℝ) (129722776779/250000000000 : ℝ) (518891107123/1000000000000 : ℝ) (512963259827/1000000000000 : ℝ) (102592651967/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 2 (129722776779/250000000000 : ℝ) (518891107123/1000000000000 : ℝ) (512963259827/1000000000000 : ℝ) (102592651967/200000000000 : ℝ) (515927183471/1000000000000 : ℝ) (515927183479/1000000000000 : ℝ) (257959334877/500000000000 : ℝ) (515918669763/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 3 (515927183471/1000000000000 : ℝ) (515927183479/1000000000000 : ℝ) (257959334877/500000000000 : ℝ) (515918669763/1000000000000 : ℝ) (128980731653/250000000000 : ℝ) (515922926621/1000000000000 : ℝ) (257961463297/500000000000 : ℝ) (128980731651/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 4 (128980731653/250000000000 : ℝ) (515922926621/1000000000000 : ℝ) (257961463297/500000000000 : ℝ) (128980731651/250000000000 : ℝ) (515922926603/1000000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 5 (515922926603/1000000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 6 (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4409/32768 : ℝ))) 7 (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4409/32768 : ℝ)) hmem 8 (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4409/32768 : ℝ))) hcmem 8 (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4409/32768 : ℝ)) (495229025359/500000000000 : ℝ) (990458050721/1000000000000 : ℝ) (257961463301/500000000000 : ℝ) (515922926613/1000000000000 : ℝ) (409108612639/500000000000 : ℝ) (818217225299/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0207_exp_lower
  have heNumeric : (252377912337/125000000000 : ℝ)/4 ≤ Real.exp (-10938887714159/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252377912337/125000000000 : ℝ)/4 ≤ Real.exp ((8817/65536 : ℝ)-(818217225299/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8817/65536 : ℝ) (4409/32768 : ℝ) (818217225299/1000000000000 : ℝ) (252377912337/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0208; no trusted numerical premise.
theorem cover7_leaf0208_exp_radius : (249399974515646577/250000000000000000 : ℝ) ≤ Real.exp ((-8819/458752 : ℝ)/8) ∧ Real.exp ((-8819/458752 : ℝ)/8) ≤ (997599898062586309/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8819/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0208_exp_lower : (918089796195179751/1000000000000000000 : ℝ) ≤ Real.exp ((-5469444860119/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469444860119/8000000000000 : ℝ)/8) ≤ (114761224524397469/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469444860119/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0208_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023045551/1000000000000 : ℝ) ≤ 4*Real.exp (4409/32768 : ℝ)*Real.exp (-mu (radius 7 (8819/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023045551/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8819/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0208_exp_radius
  have hrNumeric : (980959706277/1000000000000 : ℝ) ≤ Real.exp (-8819/458752 : ℝ) ∧ Real.exp (-8819/458752 : ℝ) ≤ (490479853139/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980959706277/1000000000000 : ℝ) ≤ (radius 7 (8819/65536 : ℝ)) ∧ (radius 7 (8819/65536 : ℝ)) ≤ (490479853139/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8819/65536 : ℝ)) (980959706277/1000000000000 : ℝ) (490479853139/500000000000 : ℝ) (12138210371/62500000000 : ℝ) (97105682971/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8819/65536 : ℝ)) (980959706277/1000000000000 : ℝ) (490479853139/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980959706277/1000000000000 : ℝ) (490479853139/500000000000 : ℝ) (495239926569/500000000000 : ℝ) (990479853139/1000000000000 : ℝ) (247608524979/250000000000 : ℝ) (990434099917/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 1 (495239926569/500000000000 : ℝ) (990479853139/1000000000000 : ℝ) (247608524979/250000000000 : ℝ) (990434099917/1000000000000 : ℝ) (990456976527/1000000000000 : ℝ) (61903561033/62500000000 : ℝ) (495228488131/500000000000 : ℝ) (123807122033/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 2 (990456976527/1000000000000 : ℝ) (61903561033/62500000000 : ℝ) (495228488131/500000000000 : ℝ) (123807122033/125000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 3 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 4 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 5 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 6 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8819/65536 : ℝ)) 7 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8819/65536 : ℝ))) (12138210371/62500000000 : ℝ) (97105682971/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12138210371/62500000000 : ℝ) (97105682971/500000000000 : ℝ) (74638210371/125000000000 : ℝ) (597105682971/1000000000000 : ℝ) (44069418641/100000000000 : ℝ) (220347093209/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 1 (74638210371/125000000000 : ℝ) (597105682971/1000000000000 : ℝ) (44069418641/100000000000 : ℝ) (220347093209/500000000000 : ℝ) (518899934689/1000000000000 : ℝ) (103779986939/200000000000 : ℝ) (256486355951/500000000000 : ℝ) (512972711909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 2 (518899934689/1000000000000 : ℝ) (103779986939/200000000000 : ℝ) (256486355951/500000000000 : ℝ) (512972711909/1000000000000 : ℝ) (103187264659/200000000000 : ℝ) (257968161651/500000000000 : ℝ) (515927811523/1000000000000 : ℝ) (51592781153/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 3 (103187264659/200000000000 : ℝ) (257968161651/500000000000 : ℝ) (515927811523/1000000000000 : ℝ) (51592781153/100000000000 : ℝ) (515932067409/1000000000000 : ℝ) (64491508427/125000000000 : ℝ) (515932067391/1000000000000 : ℝ) (515932067399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 4 (515932067409/1000000000000 : ℝ) (64491508427/125000000000 : ℝ) (515932067391/1000000000000 : ℝ) (515932067399/1000000000000 : ℝ) (2579660337/5000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 5 (2579660337/5000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 6 (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8819/65536 : ℝ))) 7 (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8819/65536 : ℝ)) hmem 8 (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8819/65536 : ℝ))) hcmem 8 (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8819/65536 : ℝ)) (495228488197/500000000000 : ℝ) (247614244099/250000000000 : ℝ) (515932067399/1000000000000 : ℝ) (32245754213/62500000000 : ℝ) (818232609451/1000000000000 : ℝ) (204558152367/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0208_exp_lower
  have heNumeric : (2019023045551/1000000000000 : ℝ)/4 ≤ Real.exp (-5469444860119/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023045551/1000000000000 : ℝ)/4 ≤ Real.exp ((4409/32768 : ℝ)-(204558152367/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4409/32768 : ℝ) (8819/65536 : ℝ) (204558152367/250000000000 : ℝ) (2019023045551/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0209; no trusted numerical premise.
theorem cover7_leaf0209_exp_radius : (3896873539993059/3906250000000000 : ℝ) ≤ Real.exp ((-315/16384 : ℝ)/8) ∧ Real.exp ((-315/16384 : ℝ)/8) ≤ (199519925247644621/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-315/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0209_exp_lower : (114761222742314359/125000000000000000 : ℝ) ≤ Real.exp ((-10938891707901/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938891707901/16000000000000 : ℝ)/8) ≤ (918089781938514873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938891707901/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0209_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201902279473/100000000000 : ℝ) ≤ 4*Real.exp (8819/65536 : ℝ)*Real.exp (-mu (radius 7 (2205/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (201902279473/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2205/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0209_exp_radius
  have hrNumeric : (245239391989/250000000000 : ℝ) ≤ Real.exp (-315/16384 : ℝ) ∧ Real.exp (-315/16384 : ℝ) ≤ (980957567957/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245239391989/250000000000 : ℝ) ≤ (radius 7 (2205/16384 : ℝ)) ∧ (radius 7 (2205/16384 : ℝ)) ≤ (980957567957/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2205/16384 : ℝ)) (245239391989/250000000000 : ℝ) (980957567957/1000000000000 : ℝ) (97111083131/500000000000 : ℝ) (194222166269/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2205/16384 : ℝ)) (245239391989/250000000000 : ℝ) (980957567957/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245239391989/250000000000 : ℝ) (980957567957/1000000000000 : ℝ) (495239391989/500000000000 : ℝ) (990478783979/1000000000000 : ℝ) (247608255107/250000000000 : ℝ) (99043302043/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 1 (495239391989/500000000000 : ℝ) (990478783979/1000000000000 : ℝ) (247608255107/250000000000 : ℝ) (99043302043/100000000000 : ℝ) (990455902203/1000000000000 : ℝ) (198091180441/200000000000 : ℝ) (495227950969/500000000000 : ℝ) (990455901941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 2 (990455902203/1000000000000 : ℝ) (198091180441/200000000000 : ℝ) (495227950969/500000000000 : ℝ) (990455901941/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 3 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 4 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 5 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 6 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2205/16384 : ℝ)) 7 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2205/16384 : ℝ))) (97111083131/500000000000 : ℝ) (194222166269/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97111083131/500000000000 : ℝ) (194222166269/1000000000000 : ℝ) (597111083131/1000000000000 : ℝ) (119422216627/200000000000 : ℝ) (88141288001/200000000000 : ℝ) (220353220007/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 1 (597111083131/1000000000000 : ℝ) (119422216627/200000000000 : ℝ) (88141288001/200000000000 : ℝ) (220353220007/500000000000 : ℝ) (16215898799/31250000000 : ℝ) (20756350463/40000000000 : ℝ) (512982163173/1000000000000 : ℝ) (512982163181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 2 (16215898799/31250000000 : ℝ) (20756350463/40000000000 : ℝ) (512982163173/1000000000000 : ℝ) (512982163181/1000000000000 : ℝ) (51594546237/100000000000 : ℝ) (257972731189/500000000000 : ℝ) (257968476271/500000000000 : ℝ) (10318739051/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 3 (51594546237/100000000000 : ℝ) (257972731189/500000000000 : ℝ) (257968476271/500000000000 : ℝ) (10318739051/20000000000 : ℝ) (16123162733/31250000000 : ℝ) (64492650933/125000000000 : ℝ) (257970603719/500000000000 : ℝ) (515941207447/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 4 (16123162733/31250000000 : ℝ) (64492650933/125000000000 : ℝ) (257970603719/500000000000 : ℝ) (515941207447/1000000000000 : ℝ) (515941207447/1000000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 5 (515941207447/1000000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 6 (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2205/16384 : ℝ))) 7 (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2205/16384 : ℝ)) hmem 8 (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2205/16384 : ℝ))) hcmem 8 (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2205/16384 : ℝ)) (99045590207/100000000000 : ℝ) (990455902073/1000000000000 : ℝ) (257970603723/500000000000 : ℝ) (16123162733/31250000000 : ℝ) (409123996233/500000000000 : ℝ) (409123996243/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0209_exp_lower
  have heNumeric : (201902279473/100000000000 : ℝ)/4 ≤ Real.exp (-10938891707901/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201902279473/100000000000 : ℝ)/4 ≤ Real.exp ((8819/65536 : ℝ)-(409123996243/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8819/65536 : ℝ) (2205/16384 : ℝ) (409123996243/500000000000 : ℝ) (201902279473/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0210; no trusted numerical premise.
theorem cover7_leaf0210_exp_radius : (498799677206966983/500000000000000000 : ℝ) ≤ Real.exp ((-8821/458752 : ℝ)/8) ∧ Real.exp ((-8821/458752 : ℝ)/8) ≤ (997599354413933967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8821/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0210_exp_lower : (183617953563430739/200000000000000000 : ℝ) ≤ Real.exp ((-109388936767/160000000000 : ℝ)/8) ∧ Real.exp ((-109388936767/160000000000 : ℝ)/8) ≤ (28690305244286053/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109388936767/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0210_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019022546289/1000000000000 : ℝ) ≤ 4*Real.exp (2205/16384 : ℝ)*Real.exp (-mu (radius 7 (8821/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019022546289/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8821/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0210_exp_radius
  have hrNumeric : (980955429641/1000000000000 : ℝ) ≤ Real.exp (-8821/458752 : ℝ) ∧ Real.exp (-8821/458752 : ℝ) ≤ (490477714821/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980955429641/1000000000000 : ℝ) ≤ (radius 7 (8821/65536 : ℝ)) ∧ (radius 7 (8821/65536 : ℝ)) ≤ (490477714821/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8821/65536 : ℝ)) (980955429641/1000000000000 : ℝ) (490477714821/500000000000 : ℝ) (97116482967/500000000000 : ℝ) (9711648297/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8821/65536 : ℝ)) (980955429641/1000000000000 : ℝ) (490477714821/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980955429641/1000000000000 : ℝ) (490477714821/500000000000 : ℝ) (49523885741/50000000000 : ℝ) (990477714821/1000000000000 : ℝ) (990431940943/1000000000000 : ℝ) (61901996309/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 1 (49523885741/50000000000 : ℝ) (990477714821/1000000000000 : ℝ) (990431940943/1000000000000 : ℝ) (61901996309/62500000000 : ℝ) (990454827881/1000000000000 : ℝ) (990454827883/1000000000000 : ℝ) (990454827617/1000000000000 : ℝ) (990454827619/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 2 (990454827881/1000000000000 : ℝ) (990454827883/1000000000000 : ℝ) (990454827617/1000000000000 : ℝ) (990454827619/1000000000000 : ℝ) (990454827749/1000000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 3 (990454827749/1000000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 4 (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 5 (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 6 (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8821/65536 : ℝ)) 7 (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8821/65536 : ℝ))) (97116482967/500000000000 : ℝ) (9711648297/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97116482967/500000000000 : ℝ) (9711648297/50000000000 : ℝ) (597116482967/1000000000000 : ℝ) (59711648297/100000000000 : ℝ) (440718692517/1000000000000 : ℝ) (110179673131/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 1 (597116482967/1000000000000 : ℝ) (59711648297/100000000000 : ℝ) (440718692517/1000000000000 : ℝ) (110179673131/250000000000 : ℝ) (259458793871/500000000000 : ℝ) (518917587747/1000000000000 : ℝ) (128247903407/250000000000 : ℝ) (102598322727/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 2 (259458793871/500000000000 : ℝ) (518917587747/1000000000000 : ℝ) (128247903407/250000000000 : ℝ) (102598322727/200000000000 : ℝ) (103190920137/200000000000 : ℝ) (515954600691/1000000000000 : ℝ) (80616577/156250000 : ℝ) (515946092807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 3 (103190920137/200000000000 : ℝ) (515954600691/1000000000000 : ℝ) (80616577/156250000 : ℝ) (515946092807/1000000000000 : ℝ) (257975173371/500000000000 : ℝ) (515950346749/1000000000000 : ℝ) (128987586681/250000000000 : ℝ) (128987586683/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 4 (257975173371/500000000000 : ℝ) (515950346749/1000000000000 : ℝ) (128987586681/250000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346733/1000000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 5 (515950346733/1000000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 6 (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8821/65536 : ℝ))) 7 (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8821/65536 : ℝ)) hmem 8 (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8821/65536 : ℝ))) hcmem 8 (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8821/65536 : ℝ)) (247613706937/250000000000 : ℝ) (990454827751/1000000000000 : ℝ) (128987586683/250000000000 : ℝ) (515950346741/1000000000000 : ℝ) (818263374307/1000000000000 : ℝ) (32730534973/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0210_exp_lower
  have heNumeric : (2019022546289/1000000000000 : ℝ)/4 ≤ Real.exp (-109388936767/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019022546289/1000000000000 : ℝ)/4 ≤ Real.exp ((2205/16384 : ℝ)-(32730534973/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2205/16384 : ℝ) (8821/65536 : ℝ) (32730534973/40000000000 : ℝ) (2019022546289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0211; no trusted numerical premise.
theorem cover7_leaf0211_exp_radius : (997599082589718893/1000000000000000000 : ℝ) ≤ Real.exp ((-4411/229376 : ℝ)/8) ∧ Real.exp ((-4411/229376 : ℝ)/8) ≤ (498799541294859447/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4411/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0211_exp_lower : (229522438457200247/250000000000000000 : ℝ) ≤ Real.exp ((-2187779125391/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187779125391/3200000000000 : ℝ)/8) ≤ (918089753828800989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187779125391/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0211_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019022300189/1000000000000 : ℝ) ≤ 4*Real.exp (8821/65536 : ℝ)*Real.exp (-mu (radius 7 (4411/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019022300189/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4411/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0211_exp_radius
  have hrNumeric : (98095329133/100000000000 : ℝ) ≤ Real.exp (-4411/229376 : ℝ) ∧ Real.exp (-4411/229376 : ℝ) ≤ (980953291331/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98095329133/100000000000 : ℝ) ≤ (radius 7 (4411/32768 : ℝ)) ∧ (radius 7 (4411/32768 : ℝ)) ≤ (980953291331/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4411/32768 : ℝ)) (98095329133/100000000000 : ℝ) (980953291331/1000000000000 : ℝ) (97121882481/500000000000 : ℝ) (24280470621/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4411/32768 : ℝ)) (98095329133/100000000000 : ℝ) (980953291331/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98095329133/100000000000 : ℝ) (980953291331/1000000000000 : ℝ) (198095329133/200000000000 : ℝ) (495238322833/500000000000 : ℝ) (495215430729/500000000000 : ℝ) (49521543073/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 1 (198095329133/200000000000 : ℝ) (495238322833/500000000000 : ℝ) (495215430729/500000000000 : ℝ) (49521543073/50000000000 : ℝ) (990453753561/1000000000000 : ℝ) (990453753563/1000000000000 : ℝ) (61903359581/62500000000 : ℝ) (990453753299/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 2 (990453753561/1000000000000 : ℝ) (990453753563/1000000000000 : ℝ) (61903359581/62500000000 : ℝ) (990453753299/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 3 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 4 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 5 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 6 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4411/32768 : ℝ)) 7 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4411/32768 : ℝ))) (97121882481/500000000000 : ℝ) (24280470621/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97121882481/500000000000 : ℝ) (24280470621/125000000000 : ℝ) (597121882481/1000000000000 : ℝ) (149280470621/250000000000 : ℝ) (440730943957/1000000000000 : ℝ) (88146188793/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 1 (597121882481/1000000000000 : ℝ) (149280470621/250000000000 : ℝ) (440730943957/1000000000000 : ℝ) (88146188793/200000000000 : ℝ) (518926413219/1000000000000 : ℝ) (20757056529/40000000000 : ℝ) (128250265819/250000000000 : ℝ) (513001063283/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 2 (518926413219/1000000000000 : ℝ) (20757056529/40000000000 : ℝ) (128250265819/250000000000 : ℝ) (513001063283/1000000000000 : ℝ) (515963738247/1000000000000 : ℝ) (257981869127/500000000000 : ℝ) (103191046461/200000000000 : ℝ) (64494404039/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 3 (515963738247/1000000000000 : ℝ) (257981869127/500000000000 : ℝ) (103191046461/200000000000 : ℝ) (64494404039/125000000000 : ℝ) (128989871319/250000000000 : ℝ) (515959485283/1000000000000 : ℝ) (257979742629/500000000000 : ℝ) (257979742633/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 4 (128989871319/250000000000 : ℝ) (515959485283/1000000000000 : ℝ) (257979742629/500000000000 : ℝ) (257979742633/500000000000 : ℝ) (515959485267/1000000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 5 (515959485267/1000000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 6 (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4411/32768 : ℝ))) 7 (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4411/32768 : ℝ)) hmem 8 (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4411/32768 : ℝ))) hcmem 8 (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4411/32768 : ℝ)) (247613438357/250000000000 : ℝ) (990453753431/1000000000000 : ℝ) (257979742633/500000000000 : ℝ) (20638379411/40000000000 : ℝ) (204569688747/250000000000 : ℝ) (163655751001/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0211_exp_lower
  have heNumeric : (2019022300189/1000000000000 : ℝ)/4 ≤ Real.exp (-2187779125391/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019022300189/1000000000000 : ℝ)/4 ≤ Real.exp ((8821/65536 : ℝ)-(163655751001/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8821/65536 : ℝ) (4411/32768 : ℝ) (163655751001/200000000000 : ℝ) (2019022300189/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0212; no trusted numerical premise.
theorem cover7_leaf0212_exp_radius : (31174962836424309/31250000000000000 : ℝ) ≤ Real.exp ((-8823/458752 : ℝ)/8) ∧ Real.exp ((-8823/458752 : ℝ)/8) ≤ (997598810765577889/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8823/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0212_exp_lower : (918089739974145313/1000000000000000000 : ℝ) ≤ Real.exp ((-1093889755857/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093889755857/1600000000000 : ℝ)/8) ≤ (459044869987072657/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093889755857/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0212_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475551411/25000000000 : ℝ) ≤ 4*Real.exp (4411/32768 : ℝ)*Real.exp (-mu (radius 7 (8823/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (50475551411/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8823/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0212_exp_radius
  have hrNumeric : (7663680883/7812500000 : ℝ) ≤ Real.exp (-8823/458752 : ℝ) ∧ Real.exp (-8823/458752 : ℝ) ≤ (39238046121/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7663680883/7812500000 : ℝ) ≤ (radius 7 (8823/65536 : ℝ)) ∧ (radius 7 (8823/65536 : ℝ)) ≤ (39238046121/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8823/65536 : ℝ)) (7663680883/7812500000 : ℝ) (39238046121/40000000000 : ℝ) (194254563341/1000000000000 : ℝ) (194254563347/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8823/65536 : ℝ)) (7663680883/7812500000 : ℝ) (39238046121/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7663680883/7812500000 : ℝ) (39238046121/40000000000 : ℝ) (15476180883/15625000000 : ℝ) (990475576513/1000000000000 : ℝ) (39617191279/40000000000 : ℝ) (123803722747/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 1 (15476180883/15625000000 : ℝ) (990475576513/1000000000000 : ℝ) (39617191279/40000000000 : ℝ) (123803722747/125000000000 : ℝ) (990452679243/1000000000000 : ℝ) (198090535849/200000000000 : ℝ) (495226339489/500000000000 : ℝ) (49522633949/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 2 (990452679243/1000000000000 : ℝ) (198090535849/200000000000 : ℝ) (495226339489/500000000000 : ℝ) (49522633949/50000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 3 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 4 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 5 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 6 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8823/65536 : ℝ)) 7 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8823/65536 : ℝ))) (194254563341/1000000000000 : ℝ) (194254563347/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194254563341/1000000000000 : ℝ) (194254563347/1000000000000 : ℝ) (59712728167/100000000000 : ℝ) (298563640837/500000000000 : ℝ) (440743194321/1000000000000 : ℝ) (440743194329/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 1 (59712728167/100000000000 : ℝ) (298563640837/500000000000 : ℝ) (440743194321/1000000000000 : ℝ) (440743194329/1000000000000 : ℝ) (103787047599/200000000000 : ℝ) (259467619001/500000000000 : ℝ) (513010512113/1000000000000 : ℝ) (513010512121/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 2 (103787047599/200000000000 : ℝ) (259467619001/500000000000 : ℝ) (513010512113/1000000000000 : ℝ) (513010512121/1000000000000 : ℝ) (257986437527/500000000000 : ℝ) (257986437531/500000000000 : ℝ) (257982185527/500000000000 : ℝ) (257982185531/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 3 (257986437527/500000000000 : ℝ) (257986437531/500000000000 : ℝ) (257982185527/500000000000 : ℝ) (257982185531/500000000000 : ℝ) (257984311527/500000000000 : ℝ) (257984311531/500000000000 : ℝ) (128992155759/250000000000 : ℝ) (103193724609/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 4 (257984311527/500000000000 : ℝ) (257984311531/500000000000 : ℝ) (128992155759/250000000000 : ℝ) (103193724609/200000000000 : ℝ) (103193724609/200000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 5 (103193724609/200000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 6 (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8823/65536 : ℝ))) 7 (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8823/65536 : ℝ)) hmem 8 (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8823/65536 : ℝ))) hcmem 8 (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8823/65536 : ℝ)) (99045267911/100000000000 : ℝ) (990452679113/1000000000000 : ℝ) (128992155761/250000000000 : ℝ) (257984311527/500000000000 : ℝ) (1636588269/2000000000 : ℝ) (20457353363/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0212_exp_lower
  have heNumeric : (50475551411/25000000000 : ℝ)/4 ≤ Real.exp (-1093889755857/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475551411/25000000000 : ℝ)/4 ≤ Real.exp ((4411/32768 : ℝ)-(20457353363/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4411/32768 : ℝ) (8823/65536 : ℝ) (20457353363/25000000000 : ℝ) (50475551411/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0213; no trusted numerical premise.
theorem cover7_leaf0213_exp_radius : (249399634735377737/250000000000000000 : ℝ) ≤ Real.exp ((-1103/57344 : ℝ)/8) ∧ Real.exp ((-1103/57344 : ℝ)/8) ≤ (997598538941510949/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1103/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0213_exp_lower : (91808972625387523/100000000000000000 : ℝ) ≤ Real.exp ((-10938899471449/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938899471449/16000000000000 : ℝ)/8) ≤ (918089726253875231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938899471449/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0213_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188863441/62500000000 : ℝ) ≤ 4*Real.exp (8823/65536 : ℝ)*Real.exp (-mu (radius 7 (1103/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (126188863441/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1103/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0213_exp_radius
  have hrNumeric : (980949014723/1000000000000 : ℝ) ≤ Real.exp (-1103/57344 : ℝ) ∧ Real.exp (-1103/57344 : ℝ) ≤ (245237253681/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980949014723/1000000000000 : ℝ) ≤ (radius 7 (1103/8192 : ℝ)) ∧ (radius 7 (1103/8192 : ℝ)) ≤ (245237253681/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1103/8192 : ℝ)) (980949014723/1000000000000 : ℝ) (245237253681/250000000000 : ℝ) (19426536107/100000000000 : ℝ) (48566340269/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1103/8192 : ℝ)) (980949014723/1000000000000 : ℝ) (245237253681/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980949014723/1000000000000 : ℝ) (245237253681/250000000000 : ℝ) (990474507361/1000000000000 : ℝ) (495237253681/500000000000 : ℝ) (990428702493/1000000000000 : ℝ) (198085740499/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 1 (990474507361/1000000000000 : ℝ) (495237253681/500000000000 : ℝ) (990428702493/1000000000000 : ℝ) (198085740499/200000000000 : ℝ) (990451604927/1000000000000 : ℝ) (990451604929/1000000000000 : ℝ) (495225802331/500000000000 : ℝ) (123806450583/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 2 (990451604927/1000000000000 : ℝ) (990451604929/1000000000000 : ℝ) (495225802331/500000000000 : ℝ) (123806450583/125000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 3 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 4 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 5 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 6 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1103/8192 : ℝ)) 7 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1103/8192 : ℝ))) (19426536107/100000000000 : ℝ) (48566340269/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19426536107/100000000000 : ℝ) (48566340269/250000000000 : ℝ) (119426536107/200000000000 : ℝ) (298566340269/500000000000 : ℝ) (440755443607/1000000000000 : ℝ) (88151088723/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 1 (119426536107/200000000000 : ℝ) (298566340269/500000000000 : ℝ) (440755443607/1000000000000 : ℝ) (88151088723/200000000000 : ℝ) (518944062071/1000000000000 : ℝ) (518944062077/1000000000000 : ℝ) (513019960139/1000000000000 : ℝ) (256509980073/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 2 (518944062071/1000000000000 : ℝ) (518944062077/1000000000000 : ℝ) (513019960139/1000000000000 : ℝ) (256509980073/500000000000 : ℝ) (103196402221/200000000000 : ℝ) (64497751389/125000000000 : ℝ) (257986754523/500000000000 : ℝ) (257986754527/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 3 (103196402221/200000000000 : ℝ) (64497751389/125000000000 : ℝ) (257986754523/500000000000 : ℝ) (257986754527/500000000000 : ℝ) (20639110403/40000000000 : ℝ) (515977760083/1000000000000 : ℝ) (515977760057/1000000000000 : ℝ) (257988880033/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 4 (20639110403/40000000000 : ℝ) (515977760083/1000000000000 : ℝ) (515977760057/1000000000000 : ℝ) (257988880033/500000000000 : ℝ) (257988880033/500000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 5 (257988880033/500000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 6 (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1103/8192 : ℝ))) 7 (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1103/8192 : ℝ)) hmem 8 (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1103/8192 : ℝ))) hcmem 8 (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1103/8192 : ℝ)) (495225802397/500000000000 : ℝ) (990451604797/1000000000000 : ℝ) (103195552013/200000000000 : ℝ) (20639110403/40000000000 : ℝ) (204577378211/250000000000 : ℝ) (25572172277/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0213_exp_lower
  have heNumeric : (126188863441/62500000000 : ℝ)/4 ≤ Real.exp (-10938899471449/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188863441/62500000000 : ℝ)/4 ≤ Real.exp ((8823/65536 : ℝ)-(25572172277/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8823/65536 : ℝ) (1103/8192 : ℝ) (25572172277/31250000000 : ℝ) (126188863441/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0214; no trusted numerical premise.
theorem cover7_leaf0214_exp_radius : (39903930684700723/40000000000000000 : ℝ) ≤ Real.exp ((-8825/458752 : ℝ)/8) ∧ Real.exp ((-8825/458752 : ℝ)/8) ≤ (249399566779379519/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8825/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0214_exp_lower : (918089712666728361/1000000000000000000 : ℝ) ≤ Real.exp ((-1367362670721/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367362670721/2000000000000 : ℝ)/8) ≤ (459044856333364181/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367362670721/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0214_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009510788007/500000000000 : ℝ) ≤ 4*Real.exp (1103/8192 : ℝ)*Real.exp (-mu (radius 7 (8825/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009510788007/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8825/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0214_exp_radius
  have hrNumeric : (490473438213/500000000000 : ℝ) ≤ Real.exp (-8825/458752 : ℝ) ∧ Real.exp (-8825/458752 : ℝ) ≤ (980946876427/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490473438213/500000000000 : ℝ) ≤ (radius 7 (8825/65536 : ℝ)) ∧ (radius 7 (8825/65536 : ℝ)) ≤ (980946876427/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8825/65536 : ℝ)) (490473438213/500000000000 : ℝ) (980946876427/1000000000000 : ℝ) (48569039539/250000000000 : ℝ) (97138079081/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8825/65536 : ℝ)) (490473438213/500000000000 : ℝ) (980946876427/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490473438213/500000000000 : ℝ) (980946876427/1000000000000 : ℝ) (990473438213/1000000000000 : ℝ) (495236719107/500000000000 : ℝ) (247606905753/250000000000 : ℝ) (990427623013/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 1 (990473438213/1000000000000 : ℝ) (495236719107/500000000000 : ℝ) (247606905753/250000000000 : ℝ) (990427623013/1000000000000 : ℝ) (247612632653/250000000000 : ℝ) (495225265307/500000000000 : ℝ) (990450530347/1000000000000 : ℝ) (990450530349/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 2 (247612632653/250000000000 : ℝ) (495225265307/500000000000 : ℝ) (990450530347/1000000000000 : ℝ) (990450530349/1000000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 3 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 4 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 5 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 6 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8825/65536 : ℝ)) 7 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8825/65536 : ℝ))) (48569039539/250000000000 : ℝ) (97138079081/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48569039539/250000000000 : ℝ) (97138079081/500000000000 : ℝ) (298569039539/500000000000 : ℝ) (597138079081/1000000000000 : ℝ) (27547980739/62500000000 : ℝ) (440767691831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 1 (298569039539/500000000000 : ℝ) (597138079081/1000000000000 : ℝ) (27547980739/62500000000 : ℝ) (440767691831/1000000000000 : ℝ) (518952885451/1000000000000 : ℝ) (32434555341/62500000000 : ℝ) (513029407359/1000000000000 : ℝ) (102605881473/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 2 (518952885451/1000000000000 : ℝ) (32434555341/62500000000 : ℝ) (513029407359/1000000000000 : ℝ) (102605881473/200000000000 : ℝ) (103198229281/200000000000 : ℝ) (515991146411/1000000000000 : ℝ) (515982646287/1000000000000 : ℝ) (257991323147/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 3 (103198229281/200000000000 : ℝ) (515991146411/1000000000000 : ℝ) (515982646287/1000000000000 : ℝ) (257991323147/500000000000 : ℝ) (257993448173/500000000000 : ℝ) (515986896353/1000000000000 : ℝ) (64498362041/125000000000 : ℝ) (103197379267/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 4 (257993448173/500000000000 : ℝ) (515986896353/1000000000000 : ℝ) (64498362041/125000000000 : ℝ) (103197379267/200000000000 : ℝ) (515986896337/1000000000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 5 (515986896337/1000000000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 6 (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8825/65536 : ℝ))) 7 (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8825/65536 : ℝ)) hmem 8 (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8825/65536 : ℝ))) hcmem 8 (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8825/65536 : ℝ)) (990450530479/1000000000000 : ℝ) (495225265241/500000000000 : ℝ) (32249181021/62500000000 : ℝ) (64498362043/125000000000 : ℝ) (51145305627/62500000000 : ℝ) (12786326407/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0214_exp_lower
  have heNumeric : (1009510788007/500000000000 : ℝ)/4 ≤ Real.exp (-1367362670721/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009510788007/500000000000 : ℝ)/4 ≤ Real.exp ((1103/8192 : ℝ)-(12786326407/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1103/8192 : ℝ) (8825/65536 : ℝ) (12786326407/15625000000 : ℝ) (1009510788007/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0215; no trusted numerical premise.
theorem cover7_leaf0215_exp_radius : (997597995293599267/1000000000000000000 : ℝ) ≤ Real.exp ((-4413/229376 : ℝ)/8) ∧ Real.exp ((-4413/229376 : ℝ)/8) ≤ (249399498823399817/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4413/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0215_exp_lower : (918089699213163743/1000000000000000000 : ℝ) ≤ Real.exp ((-10938903241463/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938903241463/16000000000000 : ℝ)/8) ≤ (28690303100411367/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938903241463/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0215_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019021339323/1000000000000 : ℝ) ≤ 4*Real.exp (8825/65536 : ℝ)*Real.exp (-mu (radius 7 (4413/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019021339323/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4413/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0215_exp_radius
  have hrNumeric : (490472369067/500000000000 : ℝ) ≤ Real.exp (-4413/229376 : ℝ) ∧ Real.exp (-4413/229376 : ℝ) ≤ (196188947627/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490472369067/500000000000 : ℝ) ≤ (radius 7 (4413/32768 : ℝ)) ∧ (radius 7 (4413/32768 : ℝ)) ≤ (196188947627/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4413/32768 : ℝ)) (490472369067/500000000000 : ℝ) (196188947627/200000000000 : ℝ) (194286954593/1000000000000 : ℝ) (194286954599/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4413/32768 : ℝ)) (490472369067/500000000000 : ℝ) (196188947627/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490472369067/500000000000 : ℝ) (196188947627/200000000000 : ℝ) (990472369067/1000000000000 : ℝ) (247618092267/250000000000 : ℝ) (247606635883/250000000000 : ℝ) (495213271767/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 1 (990472369067/1000000000000 : ℝ) (247618092267/250000000000 : ℝ) (247606635883/250000000000 : ℝ) (495213271767/500000000000 : ℝ) (990449456299/1000000000000 : ℝ) (990449456301/1000000000000 : ℝ) (495224728017/500000000000 : ℝ) (247612364009/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 2 (990449456299/1000000000000 : ℝ) (990449456301/1000000000000 : ℝ) (495224728017/500000000000 : ℝ) (247612364009/250000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 3 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 4 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 5 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 6 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4413/32768 : ℝ)) 7 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4413/32768 : ℝ))) (194286954593/1000000000000 : ℝ) (194286954599/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194286954593/1000000000000 : ℝ) (194286954599/1000000000000 : ℝ) (37321467331/62500000000 : ℝ) (5971434773/10000000000 : ℝ) (440779938963/1000000000000 : ℝ) (440779938971/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 1 (37321467331/62500000000 : ℝ) (5971434773/10000000000 : ℝ) (440779938963/1000000000000 : ℝ) (440779938971/1000000000000 : ℝ) (518961708129/1000000000000 : ℝ) (64870213517/125000000000 : ℝ) (513038853767/1000000000000 : ℝ) (256519426887/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 2 (518961708129/1000000000000 : ℝ) (64870213517/125000000000 : ℝ) (513038853767/1000000000000 : ℝ) (256519426887/500000000000 : ℝ) (129000070237/250000000000 : ℝ) (103200056191/200000000000 : ℝ) (515991782771/1000000000000 : ℝ) (515991782779/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 3 (129000070237/250000000000 : ℝ) (103200056191/200000000000 : ℝ) (515991782771/1000000000000 : ℝ) (515991782779/1000000000000 : ℝ) (515996031859/1000000000000 : ℝ) (515996031867/1000000000000 : ℝ) (257998015921/500000000000 : ℝ) (10319920637/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 4 (515996031859/1000000000000 : ℝ) (515996031867/1000000000000 : ℝ) (257998015921/500000000000 : ℝ) (10319920637/20000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 5 (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 6 (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4413/32768 : ℝ))) 7 (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4413/32768 : ℝ)) hmem 8 (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4413/32768 : ℝ))) hcmem 8 (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4413/32768 : ℝ)) (495224728083/500000000000 : ℝ) (990449456169/1000000000000 : ℝ) (10319920637/20000000000 : ℝ) (515996031859/1000000000000 : ℝ) (16366805321/20000000000 : ℝ) (204585066517/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0215_exp_lower
  have heNumeric : (2019021339323/1000000000000 : ℝ)/4 ≤ Real.exp (-10938903241463/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019021339323/1000000000000 : ℝ)/4 ≤ Real.exp ((8825/65536 : ℝ)-(204585066517/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8825/65536 : ℝ) (4413/32768 : ℝ) (204585066517/250000000000 : ℝ) (2019021339323/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0216; no trusted numerical premise.
theorem cover7_leaf0216_exp_radius : (498798861734877263/500000000000000000 : ℝ) ≤ Real.exp ((-1261/65536 : ℝ)/8) ∧ Real.exp ((-1261/65536 : ℝ)/8) ≤ (997597723469754527/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1261/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0216_exp_lower : (18361793717859037/20000000000000000 : ℝ) ≤ Real.exp ((-5469452549283/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469452549283/8000000000000 : ℝ)/8) ≤ (918089685892951851/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469452549283/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0216_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019021104977/1000000000000 : ℝ) ≤ 4*Real.exp (4413/32768 : ℝ)*Real.exp (-mu (radius 7 (8827/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019021104977/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8827/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0216_exp_radius
  have hrNumeric : (490471299923/500000000000 : ℝ) ≤ Real.exp (-1261/65536 : ℝ) ∧ Real.exp (-1261/65536 : ℝ) ≤ (980942599847/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490471299923/500000000000 : ℝ) ≤ (radius 7 (8827/65536 : ℝ)) ∧ (radius 7 (8827/65536 : ℝ)) ≤ (980942599847/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8827/65536 : ℝ)) (490471299923/500000000000 : ℝ) (980942599847/1000000000000 : ℝ) (97148875193/500000000000 : ℝ) (24287218799/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8827/65536 : ℝ)) (490471299923/500000000000 : ℝ) (980942599847/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490471299923/500000000000 : ℝ) (980942599847/1000000000000 : ℝ) (990471299923/1000000000000 : ℝ) (247617824981/250000000000 : ℝ) (990425464053/1000000000000 : ℝ) (198085092811/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 1 (990471299923/1000000000000 : ℝ) (247617824981/250000000000 : ℝ) (990425464053/1000000000000 : ℝ) (198085092811/200000000000 : ℝ) (247612095497/250000000000 : ℝ) (99044838199/100000000000 : ℝ) (495224190861/500000000000 : ℝ) (39617935269/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 2 (247612095497/250000000000 : ℝ) (99044838199/100000000000 : ℝ) (495224190861/500000000000 : ℝ) (39617935269/40000000000 : ℝ) (198089676371/200000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 3 (198089676371/200000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 4 (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 5 (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 6 (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8827/65536 : ℝ)) 7 (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8827/65536 : ℝ))) (97148875193/500000000000 : ℝ) (24287218799/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97148875193/500000000000 : ℝ) (24287218799/125000000000 : ℝ) (597148875193/1000000000000 : ℝ) (149287218799/250000000000 : ℝ) (55099023129/125000000000 : ℝ) (5509902313/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 1 (597148875193/1000000000000 : ℝ) (149287218799/250000000000 : ℝ) (55099023129/125000000000 : ℝ) (5509902313/12500000000 : ℝ) (8108914533/15625000000 : ℝ) (259485265059/500000000000 : ℝ) (513048299369/1000000000000 : ℝ) (32065518711/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 2 (8108914533/15625000000 : ℝ) (259485265059/500000000000 : ℝ) (513048299369/1000000000000 : ℝ) (32065518711/62500000000 : ℝ) (25800470737/50000000000 : ℝ) (516009414747/1000000000000 : ℝ) (516000918503/1000000000000 : ℝ) (516000918511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 3 (25800470737/50000000000 : ℝ) (516009414747/1000000000000 : ℝ) (516000918503/1000000000000 : ℝ) (516000918511/1000000000000 : ℝ) (516005166621/1000000000000 : ℝ) (516005166629/1000000000000 : ℝ) (129001291651/250000000000 : ℝ) (129001291653/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 4 (516005166621/1000000000000 : ℝ) (516005166629/1000000000000 : ℝ) (129001291651/250000000000 : ℝ) (129001291653/250000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 5 (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 6 (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8827/65536 : ℝ))) 7 (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8827/65536 : ℝ)) hmem 8 (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8827/65536 : ℝ))) hcmem 8 (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8827/65536 : ℝ)) (495224190927/500000000000 : ℝ) (495224190929/500000000000 : ℝ) (129001291653/250000000000 : ℝ) (516005166621/1000000000000 : ℝ) (818355640907/1000000000000 : ℝ) (409177820463/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0216_exp_lower
  have heNumeric : (2019021104977/1000000000000 : ℝ)/4 ≤ Real.exp (-5469452549283/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019021104977/1000000000000 : ℝ)/4 ≤ Real.exp ((4413/32768 : ℝ)-(409177820463/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4413/32768 : ℝ) (8827/65536 : ℝ) (409177820463/500000000000 : ℝ) (2019021104977/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0217; no trusted numerical premise.
theorem cover7_leaf0217_exp_radius : (997597451645983851/1000000000000000000 : ℝ) ≤ Real.exp ((-2207/114688 : ℝ)/8) ∧ Real.exp ((-2207/114688 : ℝ)/8) ≤ (249399362911495963/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2207/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0217_exp_lower : (918089672706436959/1000000000000000000 : ℝ) ≤ Real.exp ((-10938906937029/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938906937029/16000000000000 : ℝ)/8) ≤ (5738060454415231/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938906937029/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0217_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019020872983/1000000000000 : ℝ) ≤ 4*Real.exp (8827/65536 : ℝ)*Real.exp (-mu (radius 7 (2207/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019020872983/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2207/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0217_exp_radius
  have hrNumeric : (980940461563/1000000000000 : ℝ) ≤ Real.exp (-2207/114688 : ℝ) ∧ Real.exp (-2207/114688 : ℝ) ≤ (245235115391/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980940461563/1000000000000 : ℝ) ≤ (radius 7 (2207/16384 : ℝ)) ∧ (radius 7 (2207/16384 : ℝ)) ≤ (245235115391/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2207/16384 : ℝ)) (980940461563/1000000000000 : ℝ) (245235115391/250000000000 : ℝ) (194308545531/1000000000000 : ℝ) (194308545537/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2207/16384 : ℝ)) (980940461563/1000000000000 : ℝ) (245235115391/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980940461563/1000000000000 : ℝ) (245235115391/250000000000 : ℝ) (990470230781/1000000000000 : ℝ) (495235115391/500000000000 : ℝ) (15475381009/15625000000 : ℝ) (990424384577/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 1 (990470230781/1000000000000 : ℝ) (495235115391/500000000000 : ℝ) (15475381009/15625000000 : ℝ) (990424384577/1000000000000 : ℝ) (495223653839/500000000000 : ℝ) (6190295673/6250000000 : ℝ) (990447307413/1000000000000 : ℝ) (198089461483/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 2 (495223653839/500000000000 : ℝ) (6190295673/6250000000 : ℝ) (990447307413/1000000000000 : ℝ) (198089461483/200000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 3 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 4 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 5 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 6 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2207/16384 : ℝ)) 7 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2207/16384 : ℝ))) (194308545531/1000000000000 : ℝ) (194308545537/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194308545531/1000000000000 : ℝ) (194308545537/1000000000000 : ℝ) (119430854553/200000000000 : ℝ) (597154272769/1000000000000 : ℝ) (220402215013/500000000000 : ℝ) (220402215017/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 1 (119430854553/200000000000 : ℝ) (597154272769/1000000000000 : ℝ) (220402215013/500000000000 : ℝ) (220402215017/500000000000 : ℝ) (103795870279/200000000000 : ℝ) (259489675701/500000000000 : ℝ) (513057744161/1000000000000 : ℝ) (64132218021/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 2 (103795870279/200000000000 : ℝ) (259489675701/500000000000 : ℝ) (513057744161/1000000000000 : ℝ) (64132218021/125000000000 : ℝ) (258009273889/500000000000 : ℝ) (103203709557/200000000000 : ℝ) (12900251337/25000000000 : ℝ) (32250628343/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 3 (258009273889/500000000000 : ℝ) (103203709557/200000000000 : ℝ) (12900251337/25000000000 : ℝ) (32250628343/62500000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300637/1000000000000 : ℝ) (516014300611/1000000000000 : ℝ) (25800715031/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 4 (516014300629/1000000000000 : ℝ) (516014300637/1000000000000 : ℝ) (516014300611/1000000000000 : ℝ) (25800715031/50000000000 : ℝ) (25800715031/50000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 5 (25800715031/50000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 6 (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2207/16384 : ℝ))) 7 (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2207/16384 : ℝ)) hmem 8 (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2207/16384 : ℝ))) hcmem 8 (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2207/16384 : ℝ)) (198089461509/200000000000 : ℝ) (247611826887/250000000000 : ℝ) (516014300619/1000000000000 : ℝ) (516014300629/1000000000000 : ℝ) (4091855073/5000000000 : ℝ) (818371014619/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0217_exp_lower
  have heNumeric : (2019020872983/1000000000000 : ℝ)/4 ≤ Real.exp (-10938906937029/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019020872983/1000000000000 : ℝ)/4 ≤ Real.exp ((8827/65536 : ℝ)-(818371014619/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8827/65536 : ℝ) (2207/16384 : ℝ) (818371014619/1000000000000 : ℝ) (2019020872983/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0218; no trusted numerical premise.
theorem cover7_leaf0218_exp_radius : (498798589911143621/500000000000000000 : ℝ) ≤ Real.exp ((-8829/458752 : ℝ)/8) ∧ Real.exp ((-8829/458752 : ℝ)/8) ≤ (997597179822287243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8829/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0218_exp_lower : (229522414913490837/250000000000000000 : ℝ) ≤ Real.exp ((-2734727189201/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734727189201/4000000000000 : ℝ)/8) ≤ (918089659653963349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734727189201/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0218_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504755160837/250000000000 : ℝ) ≤ 4*Real.exp (2207/16384 : ℝ)*Real.exp (-mu (radius 7 (8829/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504755160837/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8829/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0218_exp_radius
  have hrNumeric : (196187664657/200000000000 : ℝ) ≤ Real.exp (-8829/458752 : ℝ) ∧ Real.exp (-8829/458752 : ℝ) ≤ (490469161643/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196187664657/200000000000 : ℝ) ≤ (radius 7 (8829/65536 : ℝ)) ∧ (radius 7 (8829/65536 : ℝ)) ≤ (490469161643/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8829/65536 : ℝ)) (196187664657/200000000000 : ℝ) (490469161643/500000000000 : ℝ) (194319340027/1000000000000 : ℝ) (194319340033/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8829/65536 : ℝ)) (196187664657/200000000000 : ℝ) (490469161643/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196187664657/200000000000 : ℝ) (490469161643/500000000000 : ℝ) (495234580821/500000000000 : ℝ) (990469161643/1000000000000 : ℝ) (990423305099/1000000000000 : ℝ) (990423305101/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 1 (495234580821/500000000000 : ℝ) (990469161643/1000000000000 : ℝ) (990423305099/1000000000000 : ℝ) (990423305101/1000000000000 : ℝ) (99044623337/100000000000 : ℝ) (247611558343/250000000000 : ℝ) (198089246621/200000000000 : ℝ) (990446233107/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 2 (99044623337/100000000000 : ℝ) (247611558343/250000000000 : ℝ) (198089246621/200000000000 : ℝ) (990446233107/1000000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 3 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 4 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 5 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 6 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8829/65536 : ℝ)) 7 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8829/65536 : ℝ))) (194319340027/1000000000000 : ℝ) (194319340033/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194319340027/1000000000000 : ℝ) (194319340033/1000000000000 : ℝ) (597159670013/1000000000000 : ℝ) (597159670017/1000000000000 : ℝ) (440816673943/1000000000000 : ℝ) (440816673951/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 1 (597159670013/1000000000000 : ℝ) (597159670017/1000000000000 : ℝ) (440816673943/1000000000000 : ℝ) (440816673951/1000000000000 : ℝ) (259494085989/500000000000 : ℝ) (32436760749/62500000000 : ℝ) (256533594071/500000000000 : ℝ) (513067188149/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 2 (259494085989/500000000000 : ℝ) (32436760749/62500000000 : ℝ) (256533594071/500000000000 : ℝ) (513067188149/1000000000000 : ℝ) (25801384003/50000000000 : ℝ) (516027680067/1000000000000 : ℝ) (516019187701/1000000000000 : ℝ) (129004796927/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 3 (25801384003/50000000000 : ℝ) (516027680067/1000000000000 : ℝ) (516019187701/1000000000000 : ℝ) (129004796927/250000000000 : ℝ) (12900585847/25000000000 : ℝ) (16125732309/31250000000 : ℝ) (516023433863/1000000000000 : ℝ) (516023433871/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 4 (12900585847/25000000000 : ℝ) (16125732309/31250000000 : ℝ) (516023433863/1000000000000 : ℝ) (516023433871/1000000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 5 (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 6 (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8829/65536 : ℝ))) 7 (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8829/65536 : ℝ)) hmem 8 (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8829/65536 : ℝ))) hcmem 8 (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8829/65536 : ℝ)) (990446233237/1000000000000 : ℝ) (24761155831/25000000000 : ℝ) (516023433871/1000000000000 : ℝ) (12900585847/25000000000 : ℝ) (409193193563/500000000000 : ℝ) (102298298393/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0218_exp_lower
  have heNumeric : (504755160837/250000000000 : ℝ)/4 ≤ Real.exp (-2734727189201/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504755160837/250000000000 : ℝ)/4 ≤ Real.exp ((2207/16384 : ℝ)-(102298298393/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2207/16384 : ℝ) (8829/65536 : ℝ) (102298298393/125000000000 : ℝ) (504755160837/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0219; no trusted numerical premise.
theorem cover7_leaf0219_exp_radius : (997596907998664699/1000000000000000000 : ℝ) ≤ Real.exp ((-4415/229376 : ℝ)/8) ∧ Real.exp ((-4415/229376 : ℝ)/8) ≤ (9975969079986647/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4415/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0219_exp_lower : (183617929347014393/200000000000000000 : ℝ) ≤ Real.exp ((-2187782111591/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187782111591/3200000000000 : ℝ)/8) ≤ (459044823367535983/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187782111591/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0219_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019020416063/1000000000000 : ℝ) ≤ 4*Real.exp (8829/65536 : ℝ)*Real.exp (-mu (radius 7 (4415/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019020416063/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4415/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0219_exp_radius
  have hrNumeric : (245234046253/250000000000 : ℝ) ≤ Real.exp (-4415/229376 : ℝ) ∧ Real.exp (-4415/229376 : ℝ) ≤ (980936185013/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245234046253/250000000000 : ℝ) ≤ (radius 7 (4415/32768 : ℝ)) ∧ (radius 7 (4415/32768 : ℝ)) ≤ (980936185013/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4415/32768 : ℝ)) (245234046253/250000000000 : ℝ) (980936185013/1000000000000 : ℝ) (1554641071/8000000000 : ℝ) (194330133881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4415/32768 : ℝ)) (245234046253/250000000000 : ℝ) (980936185013/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245234046253/250000000000 : ℝ) (980936185013/1000000000000 : ℝ) (495234046253/500000000000 : ℝ) (990468092507/1000000000000 : ℝ) (1584675561/1600000000 : ℝ) (495211112813/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 1 (495234046253/500000000000 : ℝ) (990468092507/1000000000000 : ℝ) (1584675561/1600000000 : ℝ) (495211112813/500000000000 : ℝ) (198089031813/200000000000 : ℝ) (990445159067/1000000000000 : ℝ) (990445158799/1000000000000 : ℝ) (990445158801/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 2 (198089031813/200000000000 : ℝ) (990445159067/1000000000000 : ℝ) (990445158799/1000000000000 : ℝ) (990445158801/1000000000000 : ℝ) (247611289733/250000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 3 (247611289733/250000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 4 (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 5 (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 6 (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4415/32768 : ℝ)) 7 (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4415/32768 : ℝ))) (1554641071/8000000000 : ℝ) (194330133881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1554641071/8000000000 : ℝ) (194330133881/1000000000000 : ℝ) (597165066937/1000000000000 : ℝ) (597165066941/1000000000000 : ℝ) (220414458393/500000000000 : ℝ) (220414458397/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 1 (597165066937/1000000000000 : ℝ) (597165066941/1000000000000 : ℝ) (220414458393/500000000000 : ℝ) (220414458397/500000000000 : ℝ) (518996991861/1000000000000 : ℝ) (129749247967/250000000000 : ℝ) (513076631313/1000000000000 : ℝ) (513076631321/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 2 (518996991861/1000000000000 : ℝ) (129749247967/250000000000 : ℝ) (513076631313/1000000000000 : ℝ) (513076631321/1000000000000 : ℝ) (516036811587/1000000000000 : ℝ) (103207362319/200000000000 : ℝ) (258014160583/500000000000 : ℝ) (258014160587/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 3 (516036811587/1000000000000 : ℝ) (103207362319/200000000000 : ℝ) (258014160583/500000000000 : ℝ) (258014160587/500000000000 : ℝ) (64504070797/125000000000 : ℝ) (103206513277/200000000000 : ℝ) (516032566359/1000000000000 : ℝ) (16126017699/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 4 (64504070797/125000000000 : ℝ) (103206513277/200000000000 : ℝ) (516032566359/1000000000000 : ℝ) (16126017699/31250000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 5 (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 6 (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4415/32768 : ℝ))) 7 (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4415/32768 : ℝ)) hmem 8 (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4415/32768 : ℝ))) hcmem 8 (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4415/32768 : ℝ)) (990445158931/1000000000000 : ℝ) (495222579467/500000000000 : ℝ) (516032566367/1000000000000 : ℝ) (516032566377/1000000000000 : ℝ) (409200879243/500000000000 : ℝ) (163680351701/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0219_exp_lower
  have heNumeric : (2019020416063/1000000000000 : ℝ)/4 ≤ Real.exp (-2187782111591/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019020416063/1000000000000 : ℝ)/4 ≤ Real.exp ((8829/65536 : ℝ)-(163680351701/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8829/65536 : ℝ) (4415/32768 : ℝ) (163680351701/200000000000 : ℝ) (2019020416063/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0220; no trusted numerical premise.
theorem cover7_leaf0220_exp_radius : (498798318087558111/500000000000000000 : ℝ) ≤ Real.exp ((-8831/458752 : ℝ)/8) ∧ Real.exp ((-8831/458752 : ℝ)/8) ≤ (997596636175116223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8831/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0220_exp_lower : (459044816974651881/500000000000000000 : ℝ) ≤ Real.exp ((-5469456170273/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469456170273/8000000000000 : ℝ)/8) ≤ (918089633949303763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469456170273/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0220_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25237752389/12500000000 : ℝ) ≤ 4*Real.exp (4415/32768 : ℝ)*Real.exp (-mu (radius 7 (8831/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (25237752389/12500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8831/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0220_exp_radius
  have hrNumeric : (980934046743/1000000000000 : ℝ) ≤ Real.exp (-8831/458752 : ℝ) ∧ Real.exp (-8831/458752 : ℝ) ≤ (122616755843/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980934046743/1000000000000 : ℝ) ≤ (radius 7 (8831/65536 : ℝ)) ∧ (radius 7 (8831/65536 : ℝ)) ≤ (122616755843/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8831/65536 : ℝ)) (980934046743/1000000000000 : ℝ) (122616755843/125000000000 : ℝ) (4858523177/25000000000 : ℝ) (97170463543/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8831/65536 : ℝ)) (980934046743/1000000000000 : ℝ) (122616755843/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980934046743/1000000000000 : ℝ) (122616755843/125000000000 : ℝ) (990467023371/1000000000000 : ℝ) (247616755843/250000000000 : ℝ) (19808422923/20000000000 : ℝ) (123802643269/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 1 (990467023371/1000000000000 : ℝ) (247616755843/250000000000 : ℝ) (19808422923/20000000000 : ℝ) (123802643269/125000000000 : ℝ) (24761102119/25000000000 : ℝ) (495222042381/500000000000 : ℝ) (495222042247/500000000000 : ℝ) (990444084497/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 2 (24761102119/25000000000 : ℝ) (495222042381/500000000000 : ℝ) (495222042247/500000000000 : ℝ) (990444084497/1000000000000 : ℝ) (990444084627/1000000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 3 (990444084627/1000000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 4 (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 5 (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 6 (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8831/65536 : ℝ)) 7 (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8831/65536 : ℝ))) (4858523177/25000000000 : ℝ) (97170463543/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4858523177/25000000000 : ℝ) (97170463543/500000000000 : ℝ) (29858523177/50000000000 : ℝ) (597170463543/1000000000000 : ℝ) (440841158559/1000000000000 : ℝ) (440841158567/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 1 (29858523177/50000000000 : ℝ) (597170463543/1000000000000 : ℝ) (440841158559/1000000000000 : ℝ) (440841158567/1000000000000 : ℝ) (519005811049/1000000000000 : ℝ) (103801162211/200000000000 : ℝ) (513086073679/1000000000000 : ℝ) (256543036843/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 2 (519005811049/1000000000000 : ℝ) (103801162211/200000000000 : ℝ) (513086073679/1000000000000 : ℝ) (256543036843/500000000000 : ℝ) (129011485591/250000000000 : ℝ) (516045942371/1000000000000 : ℝ) (12900936347/25000000000 : ℝ) (8063085217/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 3 (129011485591/250000000000 : ℝ) (516045942371/1000000000000 : ℝ) (12900936347/25000000000 : ℝ) (8063085217/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (51604169813/100000000000 : ℝ) (64505212263/125000000000 : ℝ) (516041698113/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 4 (258020849061/500000000000 : ℝ) (51604169813/100000000000 : ℝ) (64505212263/125000000000 : ℝ) (516041698113/1000000000000 : ℝ) (516041698113/1000000000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 5 (516041698113/1000000000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 6 (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8831/65536 : ℝ))) 7 (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8831/65536 : ℝ)) hmem 8 (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8831/65536 : ℝ))) hcmem 8 (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8831/65536 : ℝ)) (495222042313/500000000000 : ℝ) (99044408463/100000000000 : ℝ) (8063151533/15625000000 : ℝ) (258020849061/500000000000 : ℝ) (409208564343/500000000000 : ℝ) (409208564353/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0220_exp_lower
  have heNumeric : (25237752389/12500000000 : ℝ)/4 ≤ Real.exp (-5469456170273/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25237752389/12500000000 : ℝ)/4 ≤ Real.exp ((4415/32768 : ℝ)-(409208564353/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4415/32768 : ℝ) (8831/65536 : ℝ) (409208564353/500000000000 : ℝ) (25237752389/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0221; no trusted numerical premise.
theorem cover7_leaf0221_exp_radius : (997596364351641811/1000000000000000000 : ℝ) ≤ Real.exp ((-69/3584 : ℝ)/8) ∧ Real.exp ((-69/3584 : ℝ)/8) ≤ (249399091087910453/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-69/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0221_exp_lower : (918089621296658731/1000000000000000000 : ℝ) ≤ Real.exp ((-10938914104577/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938914104577/16000000000000 : ℝ)/8) ≤ (229522405324164683/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938914104577/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0221_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019968519/1000000000000 : ℝ) ≤ 4*Real.exp (8831/65536 : ℝ)*Real.exp (-mu (radius 7 (69/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019968519/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (69/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0221_exp_radius
  have hrNumeric : (490465954239/500000000000 : ℝ) ≤ Real.exp (-69/3584 : ℝ) ∧ Real.exp (-69/3584 : ℝ) ≤ (980931908479/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490465954239/500000000000 : ℝ) ≤ (radius 7 (69/512 : ℝ)) ∧ (radius 7 (69/512 : ℝ)) ≤ (980931908479/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (69/512 : ℝ)) (490465954239/500000000000 : ℝ) (980931908479/1000000000000 : ℝ) (194351719641/1000000000000 : ℝ) (194351719647/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (69/512 : ℝ)) (490465954239/500000000000 : ℝ) (980931908479/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (69/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490465954239/500000000000 : ℝ) (980931908479/1000000000000 : ℝ) (990465954239/1000000000000 : ℝ) (3095206107/3125000000 : ℝ) (990420066677/1000000000000 : ℝ) (990420066679/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (69/512 : ℝ)) 1 (990465954239/1000000000000 : ℝ) (3095206107/3125000000 : ℝ) (990420066677/1000000000000 : ℝ) (990420066679/1000000000000 : ℝ) (495221505229/500000000000 : ℝ) (49522150523/50000000000 : ℝ) (61902688137/62500000000 : ℝ) (495221505097/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (69/512 : ℝ)) 2 (495221505229/500000000000 : ℝ) (49522150523/50000000000 : ℝ) (61902688137/62500000000 : ℝ) (495221505097/500000000000 : ℝ) (39617720413/40000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (69/512 : ℝ)) 3 (39617720413/40000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (69/512 : ℝ)) 4 (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (69/512 : ℝ)) 5 (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (69/512 : ℝ)) 6 (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (69/512 : ℝ)) 7 (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (69/512 : ℝ))) (194351719641/1000000000000 : ℝ) (194351719647/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194351719641/1000000000000 : ℝ) (194351719647/1000000000000 : ℝ) (29858792991/50000000000 : ℝ) (37323491239/62500000000 : ℝ) (220426699631/500000000000 : ℝ) (440853399269/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 1 (29858792991/50000000000 : ℝ) (37323491239/62500000000 : ℝ) (220426699631/500000000000 : ℝ) (440853399269/1000000000000 : ℝ) (519014629541/1000000000000 : ℝ) (519014629547/1000000000000 : ℝ) (513095515239/1000000000000 : ℝ) (256547757623/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 2 (519014629541/1000000000000 : ℝ) (519014629547/1000000000000 : ℝ) (513095515239/1000000000000 : ℝ) (256547757623/500000000000 : ℝ) (51605507239/100000000000 : ℝ) (516055072397/1000000000000 : ℝ) (516046585843/1000000000000 : ℝ) (516046585851/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 3 (51605507239/100000000000 : ℝ) (516055072397/1000000000000 : ℝ) (516046585843/1000000000000 : ℝ) (516046585851/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (129012707281/250000000000 : ℝ) (516050829099/1000000000000 : ℝ) (516050829107/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 4 (129012707279/250000000000 : ℝ) (129012707281/250000000000 : ℝ) (516050829099/1000000000000 : ℝ) (516050829107/1000000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 5 (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 6 (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (69/512 : ℝ))) 7 (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (69/512 : ℝ)) hmem 8 (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (69/512 : ℝ))) hcmem 8 (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (69/512 : ℝ)) (247610752581/250000000000 : ℝ) (990443010327/1000000000000 : ℝ) (516050829107/1000000000000 : ℝ) (129012707279/250000000000 : ℝ) (818432497729/1000000000000 : ℝ) (818432497747/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0221_exp_lower
  have heNumeric : (2019019968519/1000000000000 : ℝ)/4 ≤ Real.exp (-10938914104577/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019968519/1000000000000 : ℝ)/4 ≤ Real.exp ((8831/65536 : ℝ)-(818432497747/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8831/65536 : ℝ) (69/512 : ℝ) (818432497747/1000000000000 : ℝ) (2019019968519/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0222; no trusted numerical premise.
theorem cover7_leaf0222_exp_radius : (997596092528241467/1000000000000000000 : ℝ) ≤ Real.exp ((-8833/458752 : ℝ)/8) ∧ Real.exp ((-8833/458752 : ℝ)/8) ≤ (249399023132060367/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8833/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0222_exp_lower : (2869030027432139/3125000000000000 : ℝ) ≤ Real.exp ((-341841120309/500000000000 : ℝ)/8) ∧ Real.exp ((-341841120309/500000000000 : ℝ)/8) ≤ (918089608778284481/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341841120309/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0222_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019748281/1000000000000 : ℝ) ≤ 4*Real.exp (69/512 : ℝ)*Real.exp (-mu (radius 7 (8833/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019748281/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8833/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0222_exp_radius
  have hrNumeric : (980929770219/1000000000000 : ℝ) ≤ Real.exp (-8833/458752 : ℝ) ∧ Real.exp (-8833/458752 : ℝ) ≤ (49046488511/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980929770219/1000000000000 : ℝ) ≤ (radius 7 (8833/65536 : ℝ)) ∧ (radius 7 (8833/65536 : ℝ)) ≤ (49046488511/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8833/65536 : ℝ)) (980929770219/1000000000000 : ℝ) (49046488511/50000000000 : ℝ) (3887250231/20000000000 : ℝ) (48590627889/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8833/65536 : ℝ)) (980929770219/1000000000000 : ℝ) (49046488511/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980929770219/1000000000000 : ℝ) (49046488511/50000000000 : ℝ) (990464885109/1000000000000 : ℝ) (99046488511/100000000000 : ℝ) (495209493603/500000000000 : ℝ) (990418987207/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 1 (990464885109/1000000000000 : ℝ) (99046488511/100000000000 : ℝ) (495209493603/500000000000 : ℝ) (990418987207/1000000000000 : ℝ) (990441936157/1000000000000 : ℝ) (990441936159/1000000000000 : ℝ) (990441935891/1000000000000 : ℝ) (990441935893/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 2 (990441936157/1000000000000 : ℝ) (990441936159/1000000000000 : ℝ) (990441935891/1000000000000 : ℝ) (990441935893/1000000000000 : ℝ) (123805242003/125000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 3 (123805242003/125000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 4 (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 5 (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 6 (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8833/65536 : ℝ)) 7 (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8833/65536 : ℝ))) (3887250231/20000000000 : ℝ) (48590627889/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3887250231/20000000000 : ℝ) (48590627889/250000000000 : ℝ) (23887250231/40000000000 : ℝ) (298590627889/500000000000 : ℝ) (88173127777/200000000000 : ℝ) (440865638893/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 1 (23887250231/40000000000 : ℝ) (298590627889/500000000000 : ℝ) (88173127777/200000000000 : ℝ) (440865638893/1000000000000 : ℝ) (51902344733/100000000000 : ℝ) (64877930917/125000000000 : ℝ) (102620991197/200000000000 : ℝ) (64138119499/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 2 (51902344733/100000000000 : ℝ) (64877930917/125000000000 : ℝ) (102620991197/200000000000 : ℝ) (64138119499/125000000000 : ℝ) (516064201657/1000000000000 : ℝ) (8063503151/15625000000 : ℝ) (516055717047/1000000000000 : ℝ) (103211143411/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 3 (516064201657/1000000000000 : ℝ) (8063503151/15625000000 : ℝ) (516055717047/1000000000000 : ℝ) (103211143411/200000000000 : ℝ) (64507494919/125000000000 : ℝ) (1612687373/3125000000 : ℝ) (258029979667/500000000000 : ℝ) (516059959343/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 4 (64507494919/125000000000 : ℝ) (1612687373/3125000000 : ℝ) (258029979667/500000000000 : ℝ) (516059959343/1000000000000 : ℝ) (516059959343/1000000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 5 (516059959343/1000000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 6 (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8833/65536 : ℝ))) 7 (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8833/65536 : ℝ)) hmem 8 (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8833/65536 : ℝ))) hcmem 8 (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8833/65536 : ℝ)) (990441936023/1000000000000 : ℝ) (495220968013/500000000000 : ℝ) (258029979671/500000000000 : ℝ) (64507494919/125000000000 : ℝ) (818447865599/1000000000000 : ℝ) (409223932809/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0222_exp_lower
  have heNumeric : (2019019748281/1000000000000 : ℝ)/4 ≤ Real.exp (-341841120309/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019748281/1000000000000 : ℝ)/4 ≤ Real.exp ((69/512 : ℝ)-(409223932809/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (69/512 : ℝ) (8833/65536 : ℝ) (409223932809/500000000000 : ℝ) (2019019748281/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0223; no trusted numerical premise.
theorem cover7_leaf0223_exp_radius : (249398955176228797/250000000000000000 : ℝ) ≤ Real.exp ((-631/32768 : ℝ)/8) ∧ Real.exp ((-631/32768 : ℝ)/8) ≤ (997595820704915189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-631/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0223_exp_lower : (918089596393148153/1000000000000000000 : ℝ) ≤ Real.exp ((-10938917576623/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938917576623/16000000000000 : ℝ)/8) ≤ (459044798196574077/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938917576623/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0223_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509765193/500000000000 : ℝ) ≤ 4*Real.exp (8833/65536 : ℝ)*Real.exp (-mu (radius 7 (4417/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509765193/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4417/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0223_exp_radius
  have hrNumeric : (245231907991/250000000000 : ℝ) ≤ Real.exp (-631/32768 : ℝ) ∧ Real.exp (-631/32768 : ℝ) ≤ (196185526393/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245231907991/250000000000 : ℝ) ≤ (radius 7 (4417/32768 : ℝ)) ∧ (radius 7 (4417/32768 : ℝ)) ≤ (196185526393/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4417/32768 : ℝ)) (245231907991/250000000000 : ℝ) (196185526393/200000000000 : ℝ) (38874660563/200000000000 : ℝ) (194373302821/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4417/32768 : ℝ)) (245231907991/250000000000 : ℝ) (196185526393/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245231907991/250000000000 : ℝ) (196185526393/200000000000 : ℝ) (495231907991/500000000000 : ℝ) (990463815983/1000000000000 : ℝ) (198083581547/200000000000 : ℝ) (990417907737/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 1 (495231907991/500000000000 : ℝ) (990463815983/1000000000000 : ℝ) (198083581547/200000000000 : ℝ) (990417907737/1000000000000 : ℝ) (495220430929/500000000000 : ℝ) (49522043093/50000000000 : ℝ) (123805107699/125000000000 : ℝ) (198088172319/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 2 (495220430929/500000000000 : ℝ) (49522043093/50000000000 : ℝ) (123805107699/125000000000 : ℝ) (198088172319/200000000000 : ℝ) (39617634469/40000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 3 (39617634469/40000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 4 (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 5 (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 6 (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4417/32768 : ℝ)) 7 (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4417/32768 : ℝ))) (38874660563/200000000000 : ℝ) (194373302821/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38874660563/200000000000 : ℝ) (194373302821/1000000000000 : ℝ) (597186651407/1000000000000 : ℝ) (597186651411/1000000000000 : ℝ) (220438938719/500000000000 : ℝ) (220438938723/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 1 (597186651407/1000000000000 : ℝ) (597186651411/1000000000000 : ℝ) (220438938719/500000000000 : ℝ) (220438938723/500000000000 : ℝ) (259516132211/500000000000 : ℝ) (519032264429/1000000000000 : ℝ) (256557197963/500000000000 : ℝ) (513114395933/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 2 (259516132211/500000000000 : ℝ) (519032264429/1000000000000 : ℝ) (256557197963/500000000000 : ℝ) (513114395933/1000000000000 : ℝ) (258036665087/500000000000 : ℝ) (516073330181/1000000000000 : ℝ) (516064847499/1000000000000 : ℝ) (516064847507/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 3 (258036665087/500000000000 : ℝ) (516073330181/1000000000000 : ℝ) (516064847499/1000000000000 : ℝ) (516064847507/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (129017272211/250000000000 : ℝ) (516069088819/1000000000000 : ℝ) (516069088827/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 4 (129017272209/250000000000 : ℝ) (129017272211/250000000000 : ℝ) (516069088819/1000000000000 : ℝ) (516069088827/1000000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 5 (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 6 (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4417/32768 : ℝ))) 7 (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4417/32768 : ℝ)) hmem 8 (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4417/32768 : ℝ))) hcmem 8 (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4417/32768 : ℝ)) (247610215431/250000000000 : ℝ) (30951276929/31250000000 : ℝ) (516069088827/1000000000000 : ℝ) (129017272209/250000000000 : ℝ) (81846323231/100000000000 : ℝ) (102307904041/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0223_exp_lower
  have heNumeric : (1009509765193/500000000000 : ℝ)/4 ≤ Real.exp (-10938917576623/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509765193/500000000000 : ℝ)/4 ≤ Real.exp ((8833/65536 : ℝ)-(102307904041/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8833/65536 : ℝ) (4417/32768 : ℝ) (102307904041/125000000000 : ℝ) (1009509765193/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0224; no trusted numerical premise.
theorem cover7_leaf0224_exp_radius : (39903821955266519/40000000000000000 : ℝ) ≤ Real.exp ((-8835/458752 : ℝ)/8) ∧ Real.exp ((-8835/458752 : ℝ)/8) ≤ (974214403204749/976562500000000 : ℝ) := by
  have h := exp_small_bounds ((-8835/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0224_exp_lower : (183617916828272901/200000000000000000 : ℝ) ≤ Real.exp ((-5469459642383/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469459642383/8000000000000 : ℝ)/8) ≤ (459044792070682253/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469459642383/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0224_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509657419/500000000000 : ℝ) ≤ 4*Real.exp (4417/32768 : ℝ)*Real.exp (-mu (radius 7 (8835/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509657419/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8835/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0224_exp_radius
  have hrNumeric : (490462746857/500000000000 : ℝ) ≤ Real.exp (-8835/458752 : ℝ) ∧ Real.exp (-8835/458752 : ℝ) ≤ (196185098743/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490462746857/500000000000 : ℝ) ≤ (radius 7 (8835/65536 : ℝ)) ∧ (radius 7 (8835/65536 : ℝ)) ≤ (196185098743/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8835/65536 : ℝ)) (490462746857/500000000000 : ℝ) (196185098743/200000000000 : ℝ) (194384093433/1000000000000 : ℝ) (194384093439/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8835/65536 : ℝ)) (490462746857/500000000000 : ℝ) (196185098743/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490462746857/500000000000 : ℝ) (196185098743/200000000000 : ℝ) (990462746857/1000000000000 : ℝ) (495231373429/500000000000 : ℝ) (495208414133/500000000000 : ℝ) (247604207067/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 1 (990462746857/1000000000000 : ℝ) (495231373429/500000000000 : ℝ) (495208414133/500000000000 : ℝ) (247604207067/250000000000 : ℝ) (990439787561/1000000000000 : ℝ) (990439787563/1000000000000 : ℝ) (198087957459/200000000000 : ℝ) (990439787297/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 2 (990439787561/1000000000000 : ℝ) (990439787563/1000000000000 : ℝ) (198087957459/200000000000 : ℝ) (990439787297/1000000000000 : ℝ) (247609946857/250000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 3 (247609946857/250000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 4 (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 5 (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 6 (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8835/65536 : ℝ)) 7 (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8835/65536 : ℝ))) (194384093433/1000000000000 : ℝ) (194384093439/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194384093433/1000000000000 : ℝ) (194384093439/1000000000000 : ℝ) (149298011679/250000000000 : ℝ) (933112573/1562500000 : ℝ) (220445057459/500000000000 : ℝ) (220445057463/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 1 (149298011679/250000000000 : ℝ) (933112573/1562500000 : ℝ) (220445057459/500000000000 : ℝ) (220445057463/500000000000 : ℝ) (519041080817/1000000000000 : ℝ) (519041080823/1000000000000 : ℝ) (256561917529/500000000000 : ℝ) (102624767013/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 2 (519041080817/1000000000000 : ℝ) (519041080823/1000000000000 : ℝ) (256561917529/500000000000 : ℝ) (102624767013/200000000000 : ℝ) (516082457937/1000000000000 : ℝ) (64510307243/125000000000 : ℝ) (258036988599/500000000000 : ℝ) (103214795441/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 3 (516082457937/1000000000000 : ℝ) (64510307243/125000000000 : ℝ) (258036988599/500000000000 : ℝ) (103214795441/200000000000 : ℝ) (516078217567/1000000000000 : ℝ) (20643128703/40000000000 : ℝ) (10321564351/20000000000 : ℝ) (258039108779/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 4 (516078217567/1000000000000 : ℝ) (20643128703/40000000000 : ℝ) (10321564351/20000000000 : ℝ) (258039108779/500000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 5 (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 6 (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8835/65536 : ℝ))) 7 (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8835/65536 : ℝ)) hmem 8 (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8835/65536 : ℝ))) hcmem 8 (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8835/65536 : ℝ)) (990439787427/1000000000000 : ℝ) (99043978743/100000000000 : ℝ) (258039108779/500000000000 : ℝ) (516078217567/1000000000000 : ℝ) (409239298929/500000000000 : ℝ) (204619649469/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0224_exp_lower
  have heNumeric : (1009509657419/500000000000 : ℝ)/4 ≤ Real.exp (-5469459642383/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509657419/500000000000 : ℝ)/4 ≤ Real.exp ((4417/32768 : ℝ)-(204619649469/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4417/32768 : ℝ) (8835/65536 : ℝ) (204619649469/250000000000 : ℝ) (1009509657419/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0200_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0200_certificate
#check SmaleRate.Proofs.cover7_leaf0201_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0201_certificate
#check SmaleRate.Proofs.cover7_leaf0202_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0202_certificate
#check SmaleRate.Proofs.cover7_leaf0203_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0203_certificate
#check SmaleRate.Proofs.cover7_leaf0204_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0204_certificate
#check SmaleRate.Proofs.cover7_leaf0205_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0205_certificate
#check SmaleRate.Proofs.cover7_leaf0206_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0206_certificate
#check SmaleRate.Proofs.cover7_leaf0207_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0207_certificate
#check SmaleRate.Proofs.cover7_leaf0208_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0208_certificate
#check SmaleRate.Proofs.cover7_leaf0209_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0209_certificate
#check SmaleRate.Proofs.cover7_leaf0210_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0210_certificate
#check SmaleRate.Proofs.cover7_leaf0211_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0211_certificate
#check SmaleRate.Proofs.cover7_leaf0212_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0212_certificate
#check SmaleRate.Proofs.cover7_leaf0213_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0213_certificate
#check SmaleRate.Proofs.cover7_leaf0214_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0214_certificate
#check SmaleRate.Proofs.cover7_leaf0215_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0215_certificate
#check SmaleRate.Proofs.cover7_leaf0216_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0216_certificate
#check SmaleRate.Proofs.cover7_leaf0217_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0217_certificate
#check SmaleRate.Proofs.cover7_leaf0218_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0218_certificate
#check SmaleRate.Proofs.cover7_leaf0219_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0219_certificate
#check SmaleRate.Proofs.cover7_leaf0220_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0220_certificate
#check SmaleRate.Proofs.cover7_leaf0221_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0221_certificate
#check SmaleRate.Proofs.cover7_leaf0222_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0222_certificate
#check SmaleRate.Proofs.cover7_leaf0223_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0223_certificate
#check SmaleRate.Proofs.cover7_leaf0224_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0224_certificate
