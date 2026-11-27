/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0450; no trusted numerical premise.
theorem cover7_leaf0450_exp_radius : (997534118726489679/1000000000000000000 : ℝ) ≤ Real.exp ((-9061/458752 : ℝ)/8) ∧ Real.exp ((-9061/458752 : ℝ)/8) ≤ (12469176484081121/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9061/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0450_exp_lower : (459045093349803851/500000000000000000 : ℝ) ≤ Real.exp ((-2734708819039/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734708819039/4000000000000 : ℝ)/8) ≤ (918090186699607703/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734708819039/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0450_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504757478951/250000000000 : ℝ) ≤ 4*Real.exp (2265/16384 : ℝ)*Real.exp (-mu (radius 7 (9061/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504757478951/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9061/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0450_exp_radius
  have hrNumeric : (196088473741/200000000000 : ℝ) ≤ Real.exp (-9061/458752 : ℝ) ∧ Real.exp (-9061/458752 : ℝ) ≤ (490221184353/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196088473741/200000000000 : ℝ) ≤ (radius 7 (9061/65536 : ℝ)) ∧ (radius 7 (9061/65536 : ℝ)) ≤ (490221184353/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9061/65536 : ℝ)) (196088473741/200000000000 : ℝ) (490221184353/500000000000 : ℝ) (196806406517/1000000000000 : ℝ) (196806406523/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9061/65536 : ℝ)) (196088473741/200000000000 : ℝ) (490221184353/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196088473741/200000000000 : ℝ) (490221184353/500000000000 : ℝ) (30944412011/31250000000 : ℝ) (990221184353/1000000000000 : ℝ) (990172898389/1000000000000 : ℝ) (99017289839/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 1 (30944412011/31250000000 : ℝ) (990221184353/1000000000000 : ℝ) (990172898389/1000000000000 : ℝ) (99017289839/100000000000 : ℝ) (99019704137/100000000000 : ℝ) (247549260343/250000000000 : ℝ) (247549260269/250000000000 : ℝ) (495098520539/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 2 (99019704137/100000000000 : ℝ) (247549260343/250000000000 : ℝ) (247549260269/250000000000 : ℝ) (495098520539/500000000000 : ℝ) (990197041223/1000000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 3 (990197041223/1000000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 4 (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 5 (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 6 (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9061/65536 : ℝ)) 7 (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9061/65536 : ℝ))) (196806406517/1000000000000 : ℝ) (196806406523/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196806406517/1000000000000 : ℝ) (196806406523/1000000000000 : ℝ) (299201601629/500000000000 : ℝ) (299201601631/500000000000 : ℝ) (443628680899/1000000000000 : ℝ) (443628680907/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 1 (299201601629/500000000000 : ℝ) (299201601631/500000000000 : ℝ) (443628680899/1000000000000 : ℝ) (443628680907/1000000000000 : ℝ) (260507971039/500000000000 : ℝ) (104203188417/200000000000 : ℝ) (103047333533/200000000000 : ℝ) (64404583459/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 2 (260507971039/500000000000 : ℝ) (104203188417/200000000000 : ℝ) (103047333533/200000000000 : ℝ) (64404583459/125000000000 : ℝ) (518126304871/1000000000000 : ℝ) (518126304879/1000000000000 : ℝ) (129529561731/250000000000 : ℝ) (129529561733/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 3 (518126304871/1000000000000 : ℝ) (518126304879/1000000000000 : ℝ) (129529561731/250000000000 : ℝ) (129529561733/250000000000 : ℝ) (518122275897/1000000000000 : ℝ) (259061137953/500000000000 : ℝ) (518122275881/1000000000000 : ℝ) (51812227589/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 4 (518122275897/1000000000000 : ℝ) (259061137953/500000000000 : ℝ) (518122275881/1000000000000 : ℝ) (51812227589/100000000000 : ℝ) (518122275889/1000000000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 5 (518122275889/1000000000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 6 (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9061/65536 : ℝ))) 7 (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9061/65536 : ℝ)) hmem 8 (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9061/65536 : ℝ))) hcmem 8 (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9061/65536 : ℝ)) (495098520611/500000000000 : ℝ) (39607881649/40000000000 : ℝ) (32382642243/62500000000 : ℝ) (259061137949/500000000000 : ℝ) (410960916823/500000000000 : ℝ) (410960916833/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0450_exp_lower
  have heNumeric : (504757478951/250000000000 : ℝ)/4 ≤ Real.exp (-2734708819039/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504757478951/250000000000 : ℝ)/4 ≤ Real.exp ((2265/16384 : ℝ)-(410960916833/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2265/16384 : ℝ) (9061/65536 : ℝ) (410960916833/500000000000 : ℝ) (504757478951/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0451; no trusted numerical premise.
theorem cover7_leaf0451_exp_radius : (997533846920049919/1000000000000000000 : ℝ) ≤ Real.exp ((-4531/229376 : ℝ)/8) ∧ Real.exp ((-4531/229376 : ℝ)/8) ≤ (779323317906289/781250000000000 : ℝ) := by
  have h := exp_small_bounds ((-4531/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0451_exp_lower : (183618040812782757/200000000000000000 : ℝ) ≤ Real.exp ((-10938832855227/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938832855227/16000000000000 : ℝ)/8) ≤ (459045102031956893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938832855227/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0451_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019030221299/1000000000000 : ℝ) ≤ 4*Real.exp (9061/65536 : ℝ)*Real.exp (-mu (radius 7 (4531/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019030221299/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4531/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0451_exp_radius
  have hrNumeric : (980440231513/1000000000000 : ℝ) ≤ Real.exp (-4531/229376 : ℝ) ∧ Real.exp (-4531/229376 : ℝ) ≤ (490220115757/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980440231513/1000000000000 : ℝ) ≤ (radius 7 (4531/32768 : ℝ)) ∧ (radius 7 (4531/32768 : ℝ)) ≤ (490220115757/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4531/32768 : ℝ)) (980440231513/1000000000000 : ℝ) (490220115757/500000000000 : ℝ) (49204263299/250000000000 : ℝ) (98408526601/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4531/32768 : ℝ)) (980440231513/1000000000000 : ℝ) (490220115757/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980440231513/1000000000000 : ℝ) (490220115757/500000000000 : ℝ) (247555028939/250000000000 : ℝ) (990220115757/1000000000000 : ℝ) (990171819187/1000000000000 : ℝ) (247542954797/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 1 (247555028939/250000000000 : ℝ) (990220115757/1000000000000 : ℝ) (990171819187/1000000000000 : ℝ) (247542954797/250000000000 : ℝ) (990195967471/1000000000000 : ℝ) (990195967473/1000000000000 : ℝ) (990195967177/1000000000000 : ℝ) (990195967179/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 2 (990195967471/1000000000000 : ℝ) (990195967473/1000000000000 : ℝ) (990195967177/1000000000000 : ℝ) (990195967179/1000000000000 : ℝ) (247548991831/250000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 3 (247548991831/250000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 4 (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 5 (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 6 (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4531/32768 : ℝ)) 7 (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4531/32768 : ℝ))) (49204263299/250000000000 : ℝ) (98408526601/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49204263299/250000000000 : ℝ) (98408526601/500000000000 : ℝ) (299204263299/500000000000 : ℝ) (598408526601/1000000000000 : ℝ) (110910170069/250000000000 : ℝ) (110910170071/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 1 (299204263299/500000000000 : ℝ) (598408526601/1000000000000 : ℝ) (110910170069/250000000000 : ℝ) (110910170071/250000000000 : ℝ) (521024603437/1000000000000 : ℝ) (521024603443/1000000000000 : ℝ) (515245927517/1000000000000 : ℝ) (515245927523/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 2 (521024603437/1000000000000 : ℝ) (521024603443/1000000000000 : ℝ) (515245927517/1000000000000 : ℝ) (515245927523/1000000000000 : ℝ) (518135265477/1000000000000 : ℝ) (518135265483/1000000000000 : ℝ) (259063604669/500000000000 : ℝ) (103625441869/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 3 (518135265477/1000000000000 : ℝ) (518135265483/1000000000000 : ℝ) (259063604669/500000000000 : ℝ) (103625441869/200000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618707/500000000000 : ℝ) (518131237391/1000000000000 : ℝ) (518131237399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 4 (518131237407/1000000000000 : ℝ) (259065618707/500000000000 : ℝ) (518131237391/1000000000000 : ℝ) (518131237399/1000000000000 : ℝ) (518131237399/1000000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 5 (518131237399/1000000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 6 (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4531/32768 : ℝ))) 7 (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4531/32768 : ℝ)) hmem 8 (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4531/32768 : ℝ))) hcmem 8 (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4531/32768 : ℝ)) (990195967323/1000000000000 : ℝ) (495097983663/500000000000 : ℝ) (259065618699/500000000000 : ℝ) (518131237407/1000000000000 : ℝ) (821936941129/1000000000000 : ℝ) (821936941147/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0451_exp_lower
  have heNumeric : (2019030221299/1000000000000 : ℝ)/4 ≤ Real.exp (-10938832855227/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019030221299/1000000000000 : ℝ)/4 ≤ Real.exp ((9061/65536 : ℝ)-(821936941147/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9061/65536 : ℝ) (4531/32768 : ℝ) (821936941147/1000000000000 : ℝ) (2019030221299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0452; no trusted numerical premise.
theorem cover7_leaf0452_exp_radius : (997533303307392583/1000000000000000000 : ℝ) ≤ Real.exp ((-1133/57344 : ℝ)/8) ∧ Real.exp ((-1133/57344 : ℝ)/8) ≤ (124691662913424073/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1133/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0452_exp_lower : (229522122014633447/250000000000000000 : ℝ) ≤ Real.exp ((-5469536050333/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469536050333/8000000000000 : ℝ)/8) ≤ (918088488058533789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469536050333/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0452_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019000031289/1000000000000 : ℝ) ≤ 4*Real.exp (4531/32768 : ℝ)*Real.exp (-mu (radius 7 (1133/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019000031289/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1133/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0452_exp_radius
  have hrNumeric : (490217978571/500000000000 : ℝ) ≤ Real.exp (-1133/57344 : ℝ) ∧ Real.exp (-1133/57344 : ℝ) ≤ (980435957143/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490217978571/500000000000 : ℝ) ≤ (radius 7 (1133/8192 : ℝ)) ∧ (radius 7 (1133/8192 : ℝ)) ≤ (980435957143/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1133/8192 : ℝ)) (490217978571/500000000000 : ℝ) (980435957143/1000000000000 : ℝ) (49209586173/250000000000 : ℝ) (196838344697/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1133/8192 : ℝ)) (490217978571/500000000000 : ℝ) (980435957143/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490217978571/500000000000 : ℝ) (980435957143/1000000000000 : ℝ) (990217978571/1000000000000 : ℝ) (247554494643/250000000000 : ℝ) (495084830393/500000000000 : ℝ) (990169660787/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 1 (990217978571/1000000000000 : ℝ) (247554494643/250000000000 : ℝ) (495084830393/500000000000 : ℝ) (990169660787/1000000000000 : ℝ) (495096909839/500000000000 : ℝ) (6188711373/6250000000 : ℝ) (990193819383/1000000000000 : ℝ) (198038763877/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 2 (495096909839/500000000000 : ℝ) (6188711373/6250000000 : ℝ) (990193819383/1000000000000 : ℝ) (198038763877/200000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 3 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 4 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 5 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 6 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1133/8192 : ℝ)) 7 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1133/8192 : ℝ))) (49209586173/250000000000 : ℝ) (196838344697/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49209586173/250000000000 : ℝ) (196838344697/1000000000000 : ℝ) (299209586173/500000000000 : ℝ) (598419172349/1000000000000 : ℝ) (110916168989/250000000000 : ℝ) (443664675963/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 1 (299209586173/500000000000 : ℝ) (598419172349/1000000000000 : ℝ) (110916168989/250000000000 : ℝ) (443664675963/1000000000000 : ℝ) (521041924151/1000000000000 : ℝ) (130260481039/250000000000 : ℝ) (257632222453/500000000000 : ℝ) (32204027807/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 2 (521041924151/1000000000000 : ℝ) (130260481039/250000000000 : ℝ) (257632222453/500000000000 : ℝ) (32204027807/62500000000 : ℝ) (32384574033/62500000000 : ℝ) (259076592267/500000000000 : ℝ) (129536283001/250000000000 : ℝ) (518145132011/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 3 (32384574033/62500000000 : ℝ) (259076592267/500000000000 : ℝ) (129536283001/250000000000 : ℝ) (518145132011/1000000000000 : ℝ) (259074579133/500000000000 : ℝ) (518149158273/1000000000000 : ℝ) (2072596633/4000000000 : ℝ) (518149158257/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 4 (259074579133/500000000000 : ℝ) (518149158273/1000000000000 : ℝ) (2072596633/4000000000 : ℝ) (518149158257/1000000000000 : ℝ) (259074579129/500000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 5 (259074579129/500000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 6 (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1133/8192 : ℝ))) 7 (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1133/8192 : ℝ)) hmem 8 (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1133/8192 : ℝ))) hcmem 8 (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1133/8192 : ℝ)) (99019381953/100000000000 : ℝ) (990193819533/1000000000000 : ℝ) (518149158257/1000000000000 : ℝ) (103629831653/200000000000 : ℝ) (821967152759/1000000000000 : ℝ) (102745894097/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0452_exp_lower
  have heNumeric : (2019000031289/1000000000000 : ℝ)/4 ≤ Real.exp (-5469536050333/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019000031289/1000000000000 : ℝ)/4 ≤ Real.exp ((4531/32768 : ℝ)-(102745894097/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4531/32768 : ℝ) (1133/8192 : ℝ) (102745894097/125000000000 : ℝ) (2019000031289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0453; no trusted numerical premise.
theorem cover7_leaf0453_exp_radius : (997532759695031491/1000000000000000000 : ℝ) ≤ Real.exp ((-4533/229376 : ℝ)/8) ∧ Real.exp ((-4533/229376 : ℝ)/8) ≤ (249383189923757873/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4533/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0453_exp_lower : (459044261839846797/500000000000000000 : ℝ) ≤ Real.exp ((-273476678359/400000000000 : ℝ)/8) ∧ Real.exp ((-273476678359/400000000000 : ℝ)/8) ≤ (183617704735938719/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273476678359/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0453_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80760026319/40000000000 : ℝ) ≤ 4*Real.exp (1133/8192 : ℝ)*Real.exp (-mu (radius 7 (4533/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (80760026319/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4533/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0453_exp_radius
  have hrNumeric : (98043168279/100000000000 : ℝ) ≤ Real.exp (-4533/229376 : ℝ) ∧ Real.exp (-4533/229376 : ℝ) ≤ (980431682791/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98043168279/100000000000 : ℝ) ≤ (radius 7 (4533/32768 : ℝ)) ∧ (radius 7 (4533/32768 : ℝ)) ≤ (980431682791/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4533/32768 : ℝ)) (98043168279/100000000000 : ℝ) (980431682791/1000000000000 : ℝ) (196859633697/1000000000000 : ℝ) (196859633703/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4533/32768 : ℝ)) (98043168279/100000000000 : ℝ) (980431682791/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98043168279/100000000000 : ℝ) (980431682791/1000000000000 : ℝ) (198043168279/200000000000 : ℝ) (247553960349/250000000000 : ℝ) (99016750239/100000000000 : ℝ) (990167502391/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 1 (198043168279/200000000000 : ℝ) (247553960349/250000000000 : ℝ) (99016750239/100000000000 : ℝ) (990167502391/1000000000000 : ℝ) (247547917973/250000000000 : ℝ) (495095835947/500000000000 : ℝ) (990191671597/1000000000000 : ℝ) (990191671599/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 2 (247547917973/250000000000 : ℝ) (495095835947/500000000000 : ℝ) (990191671597/1000000000000 : ℝ) (990191671599/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 3 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 4 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 5 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 6 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4533/32768 : ℝ)) 7 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4533/32768 : ℝ))) (196859633697/1000000000000 : ℝ) (196859633703/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196859633697/1000000000000 : ℝ) (196859633703/1000000000000 : ℝ) (37401863553/62500000000 : ℝ) (149607454213/250000000000 : ℝ) (110922166883/250000000000 : ℝ) (22184433377/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 1 (37401863553/62500000000 : ℝ) (149607454213/250000000000 : ℝ) (110922166883/250000000000 : ℝ) (22184433377/50000000000 : ℝ) (52105924219/100000000000 : ℝ) (130264810549/250000000000 : ℝ) (257641479603/500000000000 : ℝ) (515282959213/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 2 (52105924219/100000000000 : ℝ) (130264810549/250000000000 : ℝ) (257641479603/500000000000 : ℝ) (515282959213/1000000000000 : ℝ) (259085550349/500000000000 : ℝ) (103634220141/200000000000 : ℝ) (518163051787/1000000000000 : ℝ) (259081525897/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 3 (259085550349/500000000000 : ℝ) (103634220141/200000000000 : ℝ) (518163051787/1000000000000 : ℝ) (259081525897/500000000000 : ℝ) (259083538121/500000000000 : ℝ) (414533661/800000000 : ℝ) (259083538113/500000000000 : ℝ) (259083538117/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 4 (259083538121/500000000000 : ℝ) (414533661/800000000 : ℝ) (259083538113/500000000000 : ℝ) (259083538117/500000000000 : ℝ) (259083538117/500000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 5 (259083538117/500000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 6 (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4533/32768 : ℝ))) 7 (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4533/32768 : ℝ)) hmem 8 (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4533/32768 : ℝ))) hcmem 8 (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4533/32768 : ℝ)) (15471744871/15625000000 : ℝ) (990191671747/1000000000000 : ℝ) (518167076233/1000000000000 : ℝ) (259083538121/500000000000 : ℝ) (410998679971/500000000000 : ℝ) (20549933999/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0453_exp_lower
  have heNumeric : (80760026319/40000000000 : ℝ)/4 ≤ Real.exp (-273476678359/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80760026319/40000000000 : ℝ)/4 ≤ Real.exp ((1133/8192 : ℝ)-(20549933999/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1133/8192 : ℝ) (4533/32768 : ℝ) (20549933999/25000000000 : ℝ) (80760026319/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0454; no trusted numerical premise.
theorem cover7_leaf0454_exp_radius : (199506443216593329/200000000000000000 : ℝ) ≤ Real.exp ((-2267/114688 : ℝ)/8) ∧ Real.exp ((-2267/114688 : ℝ)/8) ≤ (498766108041483323/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2267/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0454_exp_lower : (18361771196200993/20000000000000000 : ℝ) ≤ Real.exp ((-5469531048531/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469531048531/8000000000000 : ℝ)/8) ≤ (918088559810049651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469531048531/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0454_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019001293619/1000000000000 : ℝ) ≤ 4*Real.exp (4533/32768 : ℝ)*Real.exp (-mu (radius 7 (2267/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019001293619/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2267/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0454_exp_radius
  have hrNumeric : (122553426057/125000000000 : ℝ) ≤ Real.exp (-2267/114688 : ℝ) ∧ Real.exp (-2267/114688 : ℝ) ≤ (980427408457/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122553426057/125000000000 : ℝ) ≤ (radius 7 (2267/16384 : ℝ)) ∧ (radius 7 (2267/16384 : ℝ)) ≤ (980427408457/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2267/16384 : ℝ)) (122553426057/125000000000 : ℝ) (980427408457/1000000000000 : ℝ) (196880920219/1000000000000 : ℝ) (7875236809/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2267/16384 : ℝ)) (122553426057/125000000000 : ℝ) (980427408457/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122553426057/125000000000 : ℝ) (980427408457/1000000000000 : ℝ) (247553426057/250000000000 : ℝ) (990213704229/1000000000000 : ℝ) (495082671999/500000000000 : ℝ) (30942667/31250000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 1 (247553426057/250000000000 : ℝ) (990213704229/1000000000000 : ℝ) (495082671999/500000000000 : ℝ) (30942667/31250000 : ℝ) (990189524113/1000000000000 : ℝ) (198037904823/200000000000 : ℝ) (990189523817/1000000000000 : ℝ) (49509476191/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 2 (990189524113/1000000000000 : ℝ) (198037904823/200000000000 : ℝ) (990189523817/1000000000000 : ℝ) (49509476191/50000000000 : ℝ) (198037904793/200000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 3 (198037904793/200000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 4 (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 5 (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 6 (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2267/16384 : ℝ)) 7 (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2267/16384 : ℝ))) (196880920219/1000000000000 : ℝ) (7875236809/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196880920219/1000000000000 : ℝ) (7875236809/40000000000 : ℝ) (598440460109/1000000000000 : ℝ) (598440460113/1000000000000 : ℝ) (443712655013/1000000000000 : ℝ) (443712655021/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 1 (598440460109/1000000000000 : ℝ) (598440460113/1000000000000 : ℝ) (443712655013/1000000000000 : ℝ) (443712655021/1000000000000 : ℝ) (521076557561/1000000000000 : ℝ) (521076557567/1000000000000 : ℝ) (64412683803/125000000000 : ℝ) (16103170951/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 2 (521076557561/1000000000000 : ℝ) (521076557567/1000000000000 : ℝ) (64412683803/125000000000 : ℝ) (16103170951/31250000000 : ℝ) (64773626749/125000000000 : ℝ) (259094507/500000000 : ℝ) (129545242173/250000000000 : ℝ) (5181809687/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 3 (64773626749/125000000000 : ℝ) (259094507/500000000 : ℝ) (129545242173/250000000000 : ℝ) (5181809687/10000000000 : ℝ) (259092495671/500000000000 : ℝ) (10363699827/20000000000 : ℝ) (259092495663/500000000000 : ℝ) (103636998267/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 4 (259092495671/500000000000 : ℝ) (10363699827/20000000000 : ℝ) (259092495663/500000000000 : ℝ) (103636998267/200000000000 : ℝ) (259092495667/500000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 5 (259092495667/500000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 6 (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2267/16384 : ℝ))) 7 (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2267/16384 : ℝ)) hmem 8 (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2267/16384 : ℝ))) hcmem 8 (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2267/16384 : ℝ)) (247547380991/250000000000 : ℝ) (966981957/976562500 : ℝ) (518184991333/1000000000000 : ℝ) (518184991343/1000000000000 : ℝ) (822027562687/1000000000000 : ℝ) (822027562707/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0454_exp_lower
  have heNumeric : (2019001293619/1000000000000 : ℝ)/4 ≤ Real.exp (-5469531048531/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019001293619/1000000000000 : ℝ)/4 ≤ Real.exp ((4533/32768 : ℝ)-(822027562707/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4533/32768 : ℝ) (2267/16384 : ℝ) (822027562707/1000000000000 : ℝ) (2019001293619/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0455; no trusted numerical premise.
theorem cover7_leaf0455_exp_radius : (249382918117799511/250000000000000000 : ℝ) ≤ Real.exp ((-4535/229376 : ℝ)/8) ∧ Real.exp ((-4535/229376 : ℝ)/8) ≤ (199506334494239609/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4535/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0455_exp_lower : (91808859645109391/100000000000000000 : ℝ) ≤ Real.exp ((-2734764247141/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734764247141/4000000000000 : ℝ)/8) ≤ (918088596451093911/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734764247141/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0455_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252375242281/125000000000 : ℝ) ≤ 4*Real.exp (2267/16384 : ℝ)*Real.exp (-mu (radius 7 (4535/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252375242281/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4535/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0455_exp_radius
  have hrNumeric : (980423134141/1000000000000 : ℝ) ≤ Real.exp (-4535/229376 : ℝ) ∧ Real.exp (-4535/229376 : ℝ) ≤ (490211567071/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980423134141/1000000000000 : ℝ) ≤ (radius 7 (4535/32768 : ℝ)) ∧ (radius 7 (4535/32768 : ℝ)) ≤ (490211567071/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4535/32768 : ℝ)) (980423134141/1000000000000 : ℝ) (490211567071/500000000000 : ℝ) (196902204251/1000000000000 : ℝ) (196902204257/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4535/32768 : ℝ)) (980423134141/1000000000000 : ℝ) (490211567071/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980423134141/1000000000000 : ℝ) (490211567071/500000000000 : ℝ) (99021156707/100000000000 : ℝ) (990211567071/1000000000000 : ℝ) (990163185611/1000000000000 : ℝ) (990163185613/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 1 (99021156707/100000000000 : ℝ) (990211567071/1000000000000 : ℝ) (990163185611/1000000000000 : ℝ) (990163185613/1000000000000 : ℝ) (49509368817/50000000000 : ℝ) (495093688171/500000000000 : ℝ) (198037475209/200000000000 : ℝ) (990187376047/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 2 (49509368817/50000000000 : ℝ) (495093688171/500000000000 : ℝ) (198037475209/200000000000 : ℝ) (990187376047/1000000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 3 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 4 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 5 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 6 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4535/32768 : ℝ)) 7 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4535/32768 : ℝ))) (196902204251/1000000000000 : ℝ) (196902204257/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196902204251/1000000000000 : ℝ) (196902204257/1000000000000 : ℝ) (4787608817/8000000000 : ℝ) (598451102129/1000000000000 : ℝ) (443736638391/1000000000000 : ℝ) (443736638399/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 1 (4787608817/8000000000 : ℝ) (598451102129/1000000000000 : ℝ) (443736638391/1000000000000 : ℝ) (443736638399/1000000000000 : ℝ) (260546935129/500000000000 : ℝ) (65136733783/125000000000 : ℝ) (103063995711/200000000000 : ℝ) (257659989281/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 2 (260546935129/500000000000 : ℝ) (65136733783/125000000000 : ℝ) (103063995711/200000000000 : ℝ) (257659989281/500000000000 : ℝ) (259103462203/500000000000 : ℝ) (518206924413/1000000000000 : ℝ) (259099441357/500000000000 : ℝ) (518198882721/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 3 (259103462203/500000000000 : ℝ) (518206924413/1000000000000 : ℝ) (259099441357/500000000000 : ℝ) (518198882721/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903567/1000000000000 : ℝ) (64775362943/125000000000 : ℝ) (506057523/976562500 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 4 (12955072589/25000000000 : ℝ) (518202903567/1000000000000 : ℝ) (64775362943/125000000000 : ℝ) (506057523/976562500 : ℝ) (506057523/976562500 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 5 (506057523/976562500 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 6 (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4535/32768 : ℝ))) 7 (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4535/32768 : ℝ)) hmem 8 (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4535/32768 : ℝ))) hcmem 8 (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4535/32768 : ℝ)) (15471677753/15625000000 : ℝ) (198037475239/200000000000 : ℝ) (518202903551/1000000000000 : ℝ) (12955072589/25000000000 : ℝ) (411028880493/500000000000 : ℝ) (205514440251/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0455_exp_lower
  have heNumeric : (252375242281/125000000000 : ℝ)/4 ≤ Real.exp (-2734764247141/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252375242281/125000000000 : ℝ)/4 ≤ Real.exp ((2267/16384 : ℝ)-(205514440251/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2267/16384 : ℝ) (4535/32768 : ℝ) (205514440251/250000000000 : ℝ) (252375242281/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0456; no trusted numerical premise.
theorem cover7_leaf0456_exp_radius : (124691391107465711/125000000000000000 : ℝ) ≤ Real.exp ((-81/4096 : ℝ)/8) ∧ Real.exp ((-81/4096 : ℝ)/8) ≤ (997531128859725689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-81/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0456_exp_lower : (459044316800782031/500000000000000000 : ℝ) ≤ Real.exp ((-5469525904521/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469525904521/8000000000000 : ℝ)/8) ≤ (918088633601564063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469525904521/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0456_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (12618766199/6250000000 : ℝ) ≤ 4*Real.exp (4535/32768 : ℝ)*Real.exp (-mu (radius 7 (567/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (12618766199/6250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (567/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0456_exp_radius
  have hrNumeric : (196083771969/200000000000 : ℝ) ≤ Real.exp (-81/4096 : ℝ) ∧ Real.exp (-81/4096 : ℝ) ≤ (490209429923/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196083771969/200000000000 : ℝ) ≤ (radius 7 (567/4096 : ℝ)) ∧ (radius 7 (567/4096 : ℝ)) ≤ (490209429923/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (567/4096 : ℝ)) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (567/4096 : ℝ)) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (567/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) (495104714961/500000000000 : ℝ) (990209429923/1000000000000 : ℝ) (990161027229/1000000000000 : ℝ) (990161027231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (567/4096 : ℝ)) 1 (495104714961/500000000000 : ℝ) (990209429923/1000000000000 : ℝ) (990161027229/1000000000000 : ℝ) (990161027231/1000000000000 : ℝ) (39607409143/40000000000 : ℝ) (990185228577/1000000000000 : ℝ) (990185228279/1000000000000 : ℝ) (495092614141/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (567/4096 : ℝ)) 2 (39607409143/40000000000 : ℝ) (990185228577/1000000000000 : ℝ) (990185228279/1000000000000 : ℝ) (495092614141/500000000000 : ℝ) (990185228427/1000000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (567/4096 : ℝ)) 3 (990185228427/1000000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (567/4096 : ℝ)) 4 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (567/4096 : ℝ)) 5 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (567/4096 : ℝ)) 6 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (567/4096 : ℝ)) 7 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (567/4096 : ℝ))) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ) (299230871449/500000000000 : ℝ) (598461742901/1000000000000 : ℝ) (443760617671/1000000000000 : ℝ) (443760617679/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 1 (299230871449/500000000000 : ℝ) (598461742901/1000000000000 : ℝ) (443760617671/1000000000000 : ℝ) (443760617679/1000000000000 : ℝ) (130277795071/250000000000 : ℝ) (52111118029/100000000000 : ℝ) (515338483601/1000000000000 : ℝ) (64417310451/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 2 (130277795071/250000000000 : ℝ) (52111118029/100000000000 : ℝ) (515338483601/1000000000000 : ℝ) (64417310451/125000000000 : ℝ) (259112415971/500000000000 : ℝ) (518224831949/1000000000000 : ℝ) (2024284351/3906250000 : ℝ) (64777099233/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 3 (259112415971/500000000000 : ℝ) (518224831949/1000000000000 : ℝ) (2024284351/3906250000 : ℝ) (64777099233/125000000000 : ℝ) (518220812899/1000000000000 : ℝ) (518220812907/1000000000000 : ℝ) (518220812883/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 4 (518220812899/1000000000000 : ℝ) (518220812907/1000000000000 : ℝ) (518220812883/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 5 (518220812891/1000000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 6 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (567/4096 : ℝ))) 7 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (567/4096 : ℝ)) hmem 8 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (567/4096 : ℝ))) hcmem 8 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (567/4096 : ℝ)) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (822087954843/1000000000000 : ℝ) (411043977431/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0456_exp_lower
  have heNumeric : (12618766199/6250000000 : ℝ)/4 ≤ Real.exp (-5469525904521/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (12618766199/6250000000 : ℝ)/4 ≤ Real.exp ((4535/32768 : ℝ)-(411043977431/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4535/32768 : ℝ) (567/4096 : ℝ) (411043977431/500000000000 : ℝ) (12618766199/6250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0457; no trusted numerical premise.
theorem cover7_leaf0457_exp_radius : (997530585248549577/1000000000000000000 : ℝ) ≤ Real.exp ((-4537/229376 : ℝ)/8) ∧ Real.exp ((-4537/229376 : ℝ)/8) ≤ (498765292624274789/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4537/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0457_exp_lower : (183617734252223177/200000000000000000 : ℝ) ≤ Real.exp ((-683690409909/1000000000000 : ℝ)/8) ∧ Real.exp ((-683690409909/1000000000000 : ℝ)/8) ≤ (459044335630557943/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683690409909/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0457_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504750813597/250000000000 : ℝ) ≤ 4*Real.exp (567/4096 : ℝ)*Real.exp (-mu (radius 7 (4537/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504750813597/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4537/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0457_exp_radius
  have hrNumeric : (980414585567/1000000000000 : ℝ) ≤ Real.exp (-4537/229376 : ℝ) ∧ Real.exp (-4537/229376 : ℝ) ≤ (30637955799/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980414585567/1000000000000 : ℝ) ≤ (radius 7 (4537/32768 : ℝ)) ∧ (radius 7 (4537/32768 : ℝ)) ≤ (30637955799/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4537/32768 : ℝ)) (980414585567/1000000000000 : ℝ) (30637955799/31250000000 : ℝ) (196944764859/1000000000000 : ℝ) (39388952973/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4537/32768 : ℝ)) (980414585567/1000000000000 : ℝ) (30637955799/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980414585567/1000000000000 : ℝ) (30637955799/31250000000 : ℝ) (990207292783/1000000000000 : ℝ) (61887955799/62500000000 : ℝ) (247539717213/250000000000 : ℝ) (990158868853/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 1 (990207292783/1000000000000 : ℝ) (61887955799/62500000000 : ℝ) (247539717213/250000000000 : ℝ) (990158868853/1000000000000 : ℝ) (990183080817/1000000000000 : ℝ) (990183080819/1000000000000 : ℝ) (990183080521/1000000000000 : ℝ) (990183080523/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 2 (990183080817/1000000000000 : ℝ) (990183080819/1000000000000 : ℝ) (990183080521/1000000000000 : ℝ) (990183080523/1000000000000 : ℝ) (990183080669/1000000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 3 (990183080669/1000000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 4 (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 5 (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 6 (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4537/32768 : ℝ)) 7 (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4537/32768 : ℝ))) (196944764859/1000000000000 : ℝ) (39388952973/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196944764859/1000000000000 : ℝ) (39388952973/200000000000 : ℝ) (598472382429/1000000000000 : ℝ) (598472382433/1000000000000 : ℝ) (221892296429/500000000000 : ℝ) (221892296433/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 1 (598472382429/1000000000000 : ℝ) (598472382433/1000000000000 : ℝ) (221892296429/500000000000 : ℝ) (221892296433/500000000000 : ℝ) (521128487643/1000000000000 : ℝ) (10422569753/20000000000 : ℝ) (515356985567/1000000000000 : ℝ) (257678492787/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 2 (521128487643/1000000000000 : ℝ) (10422569753/20000000000 : ℝ) (515356985567/1000000000000 : ℝ) (257678492787/500000000000 : ℝ) (103648547321/200000000000 : ℝ) (129560684153/250000000000 : ℝ) (518234702123/1000000000000 : ℝ) (518234702131/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 3 (103648547321/200000000000 : ℝ) (129560684153/250000000000 : ℝ) (518234702123/1000000000000 : ℝ) (518234702131/1000000000000 : ℝ) (129559679841/250000000000 : ℝ) (129559679843/250000000000 : ℝ) (129559679837/250000000000 : ℝ) (129559679839/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 4 (129559679841/250000000000 : ℝ) (129559679843/250000000000 : ℝ) (129559679837/250000000000 : ℝ) (129559679839/250000000000 : ℝ) (129559679839/250000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 5 (129559679839/250000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 6 (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4537/32768 : ℝ))) 7 (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4537/32768 : ℝ)) hmem 8 (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4537/32768 : ℝ))) hcmem 8 (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4537/32768 : ℝ)) (247545770167/250000000000 : ℝ) (990183080671/1000000000000 : ℝ) (103647743871/200000000000 : ℝ) (129559679841/250000000000 : ℝ) (411059072133/500000000000 : ℝ) (205529536071/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0457_exp_lower
  have heNumeric : (504750813597/250000000000 : ℝ)/4 ≤ Real.exp (-683690409909/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504750813597/250000000000 : ℝ)/4 ≤ Real.exp ((567/4096 : ℝ)-(205529536071/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (567/4096 : ℝ) (4537/32768 : ℝ) (205529536071/250000000000 : ℝ) (504750813597/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0458; no trusted numerical premise.
theorem cover7_leaf0458_exp_radius : (99753004163766971/100000000000000000 : ℝ) ≤ Real.exp ((-2269/114688 : ℝ)/8) ∧ Real.exp ((-2269/114688 : ℝ)/8) ≤ (997530041637669711/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2269/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0458_exp_lower : (183617741885995793/200000000000000000 : ℝ) ≤ Real.exp ((-5469520618519/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469520618519/8000000000000 : ℝ)/8) ≤ (459044354714989483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469520618519/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0458_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019003925897/1000000000000 : ℝ) ≤ 4*Real.exp (4537/32768 : ℝ)*Real.exp (-mu (radius 7 (2269/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019003925897/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2269/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0458_exp_radius
  have hrNumeric : (245102577827/250000000000 : ℝ) ≤ Real.exp (-2269/114688 : ℝ) ∧ Real.exp (-2269/114688 : ℝ) ≤ (980410311309/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245102577827/250000000000 : ℝ) ≤ (radius 7 (2269/16384 : ℝ)) ∧ (radius 7 (2269/16384 : ℝ)) ≤ (980410311309/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2269/16384 : ℝ)) (245102577827/250000000000 : ℝ) (980410311309/1000000000000 : ℝ) (49241510359/250000000000 : ℝ) (98483020721/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2269/16384 : ℝ)) (245102577827/250000000000 : ℝ) (980410311309/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245102577827/250000000000 : ℝ) (980410311309/1000000000000 : ℝ) (495102577827/500000000000 : ℝ) (198041031131/200000000000 : ℝ) (990156710479/1000000000000 : ℝ) (990156710481/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 1 (495102577827/500000000000 : ℝ) (198041031131/200000000000 : ℝ) (990156710479/1000000000000 : ℝ) (990156710481/1000000000000 : ℝ) (495090466533/500000000000 : ℝ) (247545233267/250000000000 : ℝ) (99018093277/100000000000 : ℝ) (247545233193/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 2 (495090466533/500000000000 : ℝ) (247545233267/250000000000 : ℝ) (99018093277/100000000000 : ℝ) (247545233193/250000000000 : ℝ) (495090466459/500000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 3 (495090466459/500000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 4 (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 5 (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 6 (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2269/16384 : ℝ)) 7 (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2269/16384 : ℝ))) (49241510359/250000000000 : ℝ) (98483020721/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49241510359/250000000000 : ℝ) (98483020721/500000000000 : ℝ) (299241510359/500000000000 : ℝ) (598483020721/1000000000000 : ℝ) (8876171279/20000000000 : ℝ) (221904281979/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 1 (299241510359/500000000000 : ℝ) (598483020721/1000000000000 : ℝ) (8876171279/20000000000 : ℝ) (221904281979/500000000000 : ℝ) (260572896167/500000000000 : ℝ) (26057289617/50000000000 : ℝ) (515375484451/1000000000000 : ℝ) (257687742229/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 2 (260572896167/500000000000 : ℝ) (26057289617/50000000000 : ℝ) (515375484451/1000000000000 : ℝ) (257687742229/500000000000 : ℝ) (64782579799/125000000000 : ℝ) (518260638399/1000000000000 : ℝ) (64781575939/125000000000 : ℝ) (3239078797/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 3 (64782579799/125000000000 : ℝ) (518260638399/1000000000000 : ℝ) (64781575939/125000000000 : ℝ) (3239078797/6250000000 : ℝ) (64782077869/125000000000 : ℝ) (6478207787/12500000000 : ℝ) (64782077867/125000000000 : ℝ) (16195519467/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 4 (64782077869/125000000000 : ℝ) (6478207787/12500000000 : ℝ) (64782077867/125000000000 : ℝ) (16195519467/31250000000 : ℝ) (16195519467/31250000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 5 (16195519467/31250000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 6 (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2269/16384 : ℝ))) 7 (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2269/16384 : ℝ)) hmem 8 (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2269/16384 : ℝ))) hcmem 8 (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2269/16384 : ℝ)) (990180932917/1000000000000 : ℝ) (24754523323/25000000000 : ℝ) (518256622943/1000000000000 : ℝ) (64782077869/125000000000 : ℝ) (3288593317/4000000000 : ℝ) (205537082317/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0458_exp_lower
  have heNumeric : (2019003925897/1000000000000 : ℝ)/4 ≤ Real.exp (-5469520618519/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019003925897/1000000000000 : ℝ)/4 ≤ Real.exp ((4537/32768 : ℝ)-(205537082317/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4537/32768 : ℝ) (2269/16384 : ℝ) (205537082317/250000000000 : ℝ) (2019003925897/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0459; no trusted numerical premise.
theorem cover7_leaf0459_exp_radius : (997529498027086087/1000000000000000000 : ℝ) ≤ Real.exp ((-4539/229376 : ℝ)/8) ∧ Real.exp ((-4539/229376 : ℝ)/8) ≤ (124691187253385761/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4539/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0459_exp_lower : (918088748107579559/1000000000000000000 : ℝ) ≤ Real.exp ((-2734758961151/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734758961151/4000000000000 : ℝ)/8) ≤ (22952218702689489/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734758961151/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0459_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504751151589/250000000000 : ℝ) ≤ 4*Real.exp (2269/16384 : ℝ)*Real.exp (-mu (radius 7 (4539/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504751151589/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4539/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0459_exp_radius
  have hrNumeric : (980406037067/1000000000000 : ℝ) ≤ Real.exp (-4539/229376 : ℝ) ∧ Real.exp (-4539/229376 : ℝ) ≤ (245101509267/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980406037067/1000000000000 : ℝ) ≤ (radius 7 (4539/32768 : ℝ)) ∧ (radius 7 (4539/32768 : ℝ)) ≤ (245101509267/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4539/32768 : ℝ)) (980406037067/1000000000000 : ℝ) (245101509267/250000000000 : ℝ) (49246828883/250000000000 : ℝ) (98493657769/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4539/32768 : ℝ)) (980406037067/1000000000000 : ℝ) (245101509267/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980406037067/1000000000000 : ℝ) (245101509267/250000000000 : ℝ) (990203018533/1000000000000 : ℝ) (495101509267/500000000000 : ℝ) (990154552111/1000000000000 : ℝ) (61884659507/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 1 (990203018533/1000000000000 : ℝ) (495101509267/500000000000 : ℝ) (990154552111/1000000000000 : ℝ) (61884659507/62500000000 : ℝ) (495089392661/500000000000 : ℝ) (990178785323/1000000000000 : ℝ) (39607151401/40000000000 : ℝ) (990178785027/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 2 (495089392661/500000000000 : ℝ) (990178785323/1000000000000 : ℝ) (39607151401/40000000000 : ℝ) (990178785027/1000000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 3 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 4 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 5 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 6 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4539/32768 : ℝ)) 7 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4539/32768 : ℝ))) (49246828883/250000000000 : ℝ) (98493657769/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49246828883/250000000000 : ℝ) (98493657769/500000000000 : ℝ) (299246828883/500000000000 : ℝ) (598493657769/1000000000000 : ℝ) (55479066369/125000000000 : ℝ) (5547906637/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 1 (299246828883/500000000000 : ℝ) (598493657769/1000000000000 : ℝ) (55479066369/125000000000 : ℝ) (5547906637/12500000000 : ℝ) (521163094359/1000000000000 : ℝ) (104232618873/200000000000 : ℝ) (16106061883/31250000000 : ℝ) (515393980263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 2 (521163094359/1000000000000 : ℝ) (104232618873/200000000000 : ℝ) (16106061883/31250000000 : ℝ) (515393980263/1000000000000 : ℝ) (518278537307/1000000000000 : ℝ) (259139268657/500000000000 : ℝ) (518270510027/1000000000000 : ℝ) (103654102007/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 3 (518278537307/1000000000000 : ℝ) (259139268657/500000000000 : ℝ) (518270510027/1000000000000 : ℝ) (103654102007/200000000000 : ℝ) (518274523667/1000000000000 : ℝ) (20730980947/40000000000 : ℝ) (518274523651/1000000000000 : ℝ) (518274523659/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 4 (518274523667/1000000000000 : ℝ) (20730980947/40000000000 : ℝ) (518274523651/1000000000000 : ℝ) (518274523659/1000000000000 : ℝ) (518274523659/1000000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 5 (518274523659/1000000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 6 (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4539/32768 : ℝ))) 7 (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4539/32768 : ℝ)) hmem 8 (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4539/32768 : ℝ))) hcmem 8 (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4539/32768 : ℝ)) (990178785173/1000000000000 : ℝ) (39607151407/40000000000 : ℝ) (259137261829/500000000000 : ℝ) (518274523667/1000000000000 : ℝ) (411089254901/500000000000 : ℝ) (822178509819/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0459_exp_lower
  have heNumeric : (504751151589/250000000000 : ℝ)/4 ≤ Real.exp (-2734758961151/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504751151589/250000000000 : ℝ)/4 ≤ Real.exp ((2269/16384 : ℝ)-(822178509819/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2269/16384 : ℝ) (4539/32768 : ℝ) (822178509819/1000000000000 : ℝ) (504751151589/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0460; no trusted numerical premise.
theorem cover7_leaf0460_exp_radius : (249382238604199677/250000000000000000 : ℝ) ≤ Real.exp ((-1135/57344 : ℝ)/8) ∧ Real.exp ((-1135/57344 : ℝ)/8) ≤ (997528954416798709/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1135/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0460_exp_lower : (918088787294950581/1000000000000000000 : ℝ) ≤ Real.exp ((-5469515190549/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469515190549/8000000000000 : ℝ)/8) ≤ (459044393647475291/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469515190549/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0460_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252375661973/125000000000 : ℝ) ≤ 4*Real.exp (4539/32768 : ℝ)*Real.exp (-mu (radius 7 (1135/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (252375661973/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1135/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0460_exp_radius
  have hrNumeric : (490200881423/500000000000 : ℝ) ≤ Real.exp (-1135/57344 : ℝ) ∧ Real.exp (-1135/57344 : ℝ) ≤ (980401762847/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490200881423/500000000000 : ℝ) ≤ (radius 7 (1135/8192 : ℝ)) ∧ (radius 7 (1135/8192 : ℝ)) ≤ (980401762847/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1135/8192 : ℝ)) (490200881423/500000000000 : ℝ) (980401762847/1000000000000 : ℝ) (98504293569/500000000000 : ℝ) (24626073393/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1135/8192 : ℝ)) (490200881423/500000000000 : ℝ) (980401762847/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490200881423/500000000000 : ℝ) (980401762847/1000000000000 : ℝ) (990200881423/1000000000000 : ℝ) (61887555089/62500000000 : ℝ) (247538098437/250000000000 : ℝ) (158424383/160000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 1 (990200881423/1000000000000 : ℝ) (61887555089/62500000000 : ℝ) (247538098437/250000000000 : ℝ) (158424383/160000000 : ℝ) (198035327517/200000000000 : ℝ) (990176637587/1000000000000 : ℝ) (123772079661/125000000000 : ℝ) (990176637291/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 2 (198035327517/200000000000 : ℝ) (990176637587/1000000000000 : ℝ) (123772079661/125000000000 : ℝ) (990176637291/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 3 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 4 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 5 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 6 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1135/8192 : ℝ)) 7 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1135/8192 : ℝ))) (98504293569/500000000000 : ℝ) (24626073393/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98504293569/500000000000 : ℝ) (24626073393/125000000000 : ℝ) (598504293569/1000000000000 : ℝ) (149626073393/250000000000 : ℝ) (88771298771/200000000000 : ℝ) (443856493863/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 1 (598504293569/1000000000000 : ℝ) (149626073393/250000000000 : ℝ) (88771298771/200000000000 : ℝ) (443856493863/1000000000000 : ℝ) (32573774607/62500000000 : ℝ) (260590196859/500000000000 : ℝ) (515412472977/1000000000000 : ℝ) (64426559123/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 2 (32573774607/62500000000 : ℝ) (260590196859/500000000000 : ℝ) (515412472977/1000000000000 : ℝ) (64426559123/125000000000 : ℝ) (8098381771/15625000000 : ℝ) (518296433351/1000000000000 : ℝ) (259144204831/500000000000 : ℝ) (518288409669/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 3 (8098381771/15625000000 : ℝ) (518296433351/1000000000000 : ℝ) (259144204831/500000000000 : ℝ) (518288409669/1000000000000 : ℝ) (518292421503/1000000000000 : ℝ) (51829242151/100000000000 : ℝ) (518292421487/1000000000000 : ℝ) (103658484299/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 4 (518292421503/1000000000000 : ℝ) (51829242151/100000000000 : ℝ) (518292421487/1000000000000 : ℝ) (103658484299/200000000000 : ℝ) (103658484299/200000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 5 (103658484299/200000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 6 (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1135/8192 : ℝ))) 7 (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1135/8192 : ℝ)) hmem 8 (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1135/8192 : ℝ))) hcmem 8 (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1135/8192 : ℝ)) (247544159359/250000000000 : ℝ) (990176637439/1000000000000 : ℝ) (259146210747/500000000000 : ℝ) (518292421503/1000000000000 : ℝ) (82220868591/100000000000 : ℝ) (102776085741/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0460_exp_lower
  have heNumeric : (252375661973/125000000000 : ℝ)/4 ≤ Real.exp (-5469515190549/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252375661973/125000000000 : ℝ)/4 ≤ Real.exp ((4539/32768 : ℝ)-(102776085741/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4539/32768 : ℝ) (1135/8192 : ℝ) (102776085741/125000000000 : ℝ) (252375661973/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0461; no trusted numerical premise.
theorem cover7_leaf0461_exp_radius : (498764205403403787/500000000000000000 : ℝ) ≤ Real.exp ((-4541/229376 : ℝ)/8) ∧ Real.exp ((-4541/229376 : ℝ)/8) ≤ (39901136432272303/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4541/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0461_exp_lower : (459044413495242721/500000000000000000 : ℝ) ≤ Real.exp ((-1367378105843/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367378105843/2000000000000 : ℝ)/8) ≤ (918088826990485443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367378105843/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0461_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252375749269/125000000000 : ℝ) ≤ 4*Real.exp (1135/8192 : ℝ)*Real.exp (-mu (radius 7 (4541/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252375749269/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4541/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0461_exp_radius
  have hrNumeric : (980397488643/1000000000000 : ℝ) ≤ Real.exp (-4541/229376 : ℝ) ∧ Real.exp (-4541/229376 : ℝ) ≤ (245099372161/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980397488643/1000000000000 : ℝ) ≤ (radius 7 (4541/32768 : ℝ)) ∧ (radius 7 (4541/32768 : ℝ)) ≤ (245099372161/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4541/32768 : ℝ)) (980397488643/1000000000000 : ℝ) (245099372161/250000000000 : ℝ) (98514928133/500000000000 : ℝ) (12314366017/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4541/32768 : ℝ)) (980397488643/1000000000000 : ℝ) (245099372161/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980397488643/1000000000000 : ℝ) (245099372161/250000000000 : ℝ) (990198744321/1000000000000 : ℝ) (495099372161/500000000000 : ℝ) (99015023539/100000000000 : ℝ) (990150235391/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 1 (990198744321/1000000000000 : ℝ) (495099372161/500000000000 : ℝ) (99015023539/100000000000 : ℝ) (990150235391/1000000000000 : ℝ) (198034897971/200000000000 : ℝ) (990174489857/1000000000000 : ℝ) (495087244779/500000000000 : ℝ) (24754362239/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 2 (198034897971/200000000000 : ℝ) (990174489857/1000000000000 : ℝ) (495087244779/500000000000 : ℝ) (24754362239/25000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 3 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 4 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 5 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 6 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4541/32768 : ℝ)) 7 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4541/32768 : ℝ))) (98514928133/500000000000 : ℝ) (12314366017/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98514928133/500000000000 : ℝ) (12314366017/62500000000 : ℝ) (598514928133/1000000000000 : ℝ) (74814366017/125000000000 : ℝ) (443880452673/1000000000000 : ℝ) (443880452681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 1 (598514928133/1000000000000 : ℝ) (74814366017/125000000000 : ℝ) (443880452673/1000000000000 : ℝ) (443880452681/1000000000000 : ℝ) (521197690403/1000000000000 : ℝ) (521197690409/1000000000000 : ℝ) (515430962623/1000000000000 : ℝ) (51543096263/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 2 (521197690403/1000000000000 : ℝ) (521197690409/1000000000000 : ℝ) (515430962623/1000000000000 : ℝ) (51543096263/100000000000 : ℝ) (518314326513/1000000000000 : ℝ) (12957858163/25000000000 : ℝ) (259153153213/500000000000 : ℝ) (518306306433/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 3 (518314326513/1000000000000 : ℝ) (12957858163/25000000000 : ℝ) (259153153213/500000000000 : ℝ) (518306306433/1000000000000 : ℝ) (518310316469/1000000000000 : ℝ) (518310316477/1000000000000 : ℝ) (518310316453/1000000000000 : ℝ) (518310316461/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 4 (518310316469/1000000000000 : ℝ) (518310316477/1000000000000 : ℝ) (518310316453/1000000000000 : ℝ) (518310316461/1000000000000 : ℝ) (518310316461/1000000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 5 (518310316461/1000000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 6 (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4541/32768 : ℝ))) 7 (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4541/32768 : ℝ)) hmem 8 (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4541/32768 : ℝ))) hcmem 8 (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4541/32768 : ℝ)) (495087244853/500000000000 : ℝ) (990174489709/1000000000000 : ℝ) (25915515823/50000000000 : ℝ) (518310316469/1000000000000 : ℝ) (102779857199/125000000000 : ℝ) (822238857609/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0461_exp_lower
  have heNumeric : (252375749269/125000000000 : ℝ)/4 ≤ Real.exp (-1367378105843/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252375749269/125000000000 : ℝ)/4 ≤ Real.exp ((1135/8192 : ℝ)-(822238857609/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1135/8192 : ℝ) (4541/32768 : ℝ) (822238857609/1000000000000 : ℝ) (252375749269/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0462; no trusted numerical premise.
theorem cover7_leaf0462_exp_radius : (997527867197112683/1000000000000000000 : ℝ) ≤ Real.exp ((-2271/114688 : ℝ)/8) ∧ Real.exp ((-2271/114688 : ℝ)/8) ≤ (249381966799278171/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2271/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0462_exp_lower : (22952221679837391/25000000000000000 : ℝ) ≤ Real.exp ((-5469509620819/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469509620819/8000000000000 : ℝ)/8) ≤ (918088867193495641/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469509620819/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0462_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019006701449/1000000000000 : ℝ) ≤ 4*Real.exp (4541/32768 : ℝ)*Real.exp (-mu (radius 7 (2271/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019006701449/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2271/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0462_exp_radius
  have hrNumeric : (490196607229/500000000000 : ℝ) ≤ Real.exp (-2271/114688 : ℝ) ∧ Real.exp (-2271/114688 : ℝ) ≤ (980393214459/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490196607229/500000000000 : ℝ) ≤ (radius 7 (2271/16384 : ℝ)) ∧ (radius 7 (2271/16384 : ℝ)) ≤ (980393214459/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2271/16384 : ℝ)) (490196607229/500000000000 : ℝ) (980393214459/1000000000000 : ℝ) (49262780729/250000000000 : ℝ) (98525561461/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2271/16384 : ℝ)) (490196607229/500000000000 : ℝ) (980393214459/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490196607229/500000000000 : ℝ) (980393214459/1000000000000 : ℝ) (990196607229/1000000000000 : ℝ) (99019660723/100000000000 : ℝ) (198029615407/200000000000 : ℝ) (990148077037/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 1 (990196607229/1000000000000 : ℝ) (99019660723/100000000000 : ℝ) (198029615407/200000000000 : ℝ) (990148077037/1000000000000 : ℝ) (247543085533/250000000000 : ℝ) (495086171067/500000000000 : ℝ) (495086170917/500000000000 : ℝ) (990172341837/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 2 (247543085533/250000000000 : ℝ) (495086171067/500000000000 : ℝ) (495086170917/500000000000 : ℝ) (990172341837/1000000000000 : ℝ) (990172341983/1000000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 3 (990172341983/1000000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 4 (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 5 (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 6 (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2271/16384 : ℝ)) 7 (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2271/16384 : ℝ))) (49262780729/250000000000 : ℝ) (98525561461/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49262780729/250000000000 : ℝ) (98525561461/500000000000 : ℝ) (299262780729/500000000000 : ℝ) (598525561461/1000000000000 : ℝ) (443904407407/1000000000000 : ℝ) (88780881483/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 1 (299262780729/500000000000 : ℝ) (598525561461/1000000000000 : ℝ) (443904407407/1000000000000 : ℝ) (88780881483/200000000000 : ℝ) (32575936527/62500000000 : ℝ) (260607492219/500000000000 : ℝ) (128862362299/250000000000 : ℝ) (515449449203/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 2 (32575936527/62500000000 : ℝ) (260607492219/500000000000 : ℝ) (128862362299/250000000000 : ℝ) (515449449203/1000000000000 : ℝ) (259166108407/500000000000 : ℝ) (518332216821/1000000000000 : ℝ) (809881563/1562500000 : ℝ) (64790525041/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 3 (259166108407/500000000000 : ℝ) (518332216821/1000000000000 : ℝ) (809881563/1562500000 : ℝ) (64790525041/125000000000 : ℝ) (518328208567/1000000000000 : ℝ) (20733128343/40000000000 : ℝ) (518328208551/1000000000000 : ℝ) (6479102607/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 4 (518328208567/1000000000000 : ℝ) (20733128343/40000000000 : ℝ) (518328208551/1000000000000 : ℝ) (6479102607/12500000000 : ℝ) (518328208559/1000000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 5 (518328208559/1000000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 6 (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2271/16384 : ℝ))) 7 (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2271/16384 : ℝ)) hmem 8 (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2271/16384 : ℝ))) hcmem 8 (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2271/16384 : ℝ)) (495086170991/500000000000 : ℝ) (495086170993/500000000000 : ℝ) (259164104279/500000000000 : ℝ) (64791026071/125000000000 : ℝ) (51391814053/62500000000 : ℝ) (205567256217/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0462_exp_lower
  have heNumeric : (2019006701449/1000000000000 : ℝ)/4 ≤ Real.exp (-5469509620819/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019006701449/1000000000000 : ℝ)/4 ≤ Real.exp ((4541/32768 : ℝ)-(205567256217/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4541/32768 : ℝ) (2271/16384 : ℝ) (205567256217/250000000000 : ℝ) (2019006701449/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0463; no trusted numerical premise.
theorem cover7_leaf0463_exp_radius : (249381830896928509/250000000000000000 : ℝ) ≤ Real.exp ((-649/32768 : ℝ)/8) ∧ Real.exp ((-649/32768 : ℝ)/8) ≤ (997527323587714037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-649/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0463_exp_lower : (183617781581048723/200000000000000000 : ℝ) ≤ Real.exp ((-2734753391401/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734753391401/4000000000000 : ℝ)/8) ≤ (28690278372038863/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734753391401/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0463_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63093981803/31250000000 : ℝ) ≤ 4*Real.exp (2271/16384 : ℝ)*Real.exp (-mu (radius 7 (4543/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (63093981803/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4543/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0463_exp_radius
  have hrNumeric : (245097235073/250000000000 : ℝ) ≤ Real.exp (-649/32768 : ℝ) ∧ Real.exp (-649/32768 : ℝ) ≤ (980388940293/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245097235073/250000000000 : ℝ) ≤ (radius 7 (4543/32768 : ℝ)) ∧ (radius 7 (4543/32768 : ℝ)) ≤ (980388940293/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4543/32768 : ℝ)) (245097235073/250000000000 : ℝ) (980388940293/1000000000000 : ℝ) (49268096771/250000000000 : ℝ) (19707238709/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4543/32768 : ℝ)) (245097235073/250000000000 : ℝ) (980388940293/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245097235073/250000000000 : ℝ) (980388940293/1000000000000 : ℝ) (495097235073/500000000000 : ℝ) (990194470147/1000000000000 : ℝ) (495072959343/500000000000 : ℝ) (30942059959/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 1 (495097235073/500000000000 : ℝ) (990194470147/1000000000000 : ℝ) (495072959343/500000000000 : ℝ) (30942059959/31250000000 : ℝ) (61885637151/62500000000 : ℝ) (495085097209/500000000000 : ℝ) (495085097059/500000000000 : ℝ) (24754254853/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 2 (61885637151/62500000000 : ℝ) (495085097209/500000000000 : ℝ) (495085097059/500000000000 : ℝ) (24754254853/25000000000 : ℝ) (990170194267/1000000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 3 (990170194267/1000000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 4 (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 5 (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 6 (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4543/32768 : ℝ)) 7 (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4543/32768 : ℝ))) (49268096771/250000000000 : ℝ) (19707238709/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49268096771/250000000000 : ℝ) (19707238709/100000000000 : ℝ) (299268096771/500000000000 : ℝ) (119707238709/200000000000 : ℝ) (443928358053/1000000000000 : ℝ) (443928358061/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 1 (299268096771/500000000000 : ℝ) (119707238709/200000000000 : ℝ) (443928358053/1000000000000 : ℝ) (443928358061/1000000000000 : ℝ) (521232275797/1000000000000 : ℝ) (521232275803/1000000000000 : ℝ) (128866983173/250000000000 : ℝ) (515467932699/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 2 (521232275797/1000000000000 : ℝ) (521232275803/1000000000000 : ℝ) (128866983173/250000000000 : ℝ) (515467932699/1000000000000 : ℝ) (129587526061/250000000000 : ℝ) (518350104251/1000000000000 : ℝ) (259171045671/500000000000 : ℝ) (10366841827/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 3 (129587526061/250000000000 : ℝ) (518350104251/1000000000000 : ℝ) (259171045671/500000000000 : ℝ) (10366841827/20000000000 : ℝ) (518346097793/1000000000000 : ℝ) (518346097801/1000000000000 : ℝ) (518346097777/1000000000000 : ℝ) (259173048893/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 4 (518346097793/1000000000000 : ℝ) (518346097801/1000000000000 : ℝ) (518346097777/1000000000000 : ℝ) (259173048893/500000000000 : ℝ) (103669219557/200000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 5 (103669219557/200000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 6 (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4543/32768 : ℝ))) 7 (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4543/32768 : ℝ)) hmem 8 (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4543/32768 : ℝ))) hcmem 8 (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4543/32768 : ℝ)) (495085097133/500000000000 : ℝ) (990170194269/1000000000000 : ℝ) (64793262223/125000000000 : ℝ) (259173048897/500000000000 : ℝ) (32891967507/40000000000 : ℝ) (411149593847/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0463_exp_lower
  have heNumeric : (63093981803/31250000000 : ℝ)/4 ≤ Real.exp (-2734753391401/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63093981803/31250000000 : ℝ)/4 ≤ Real.exp ((2271/16384 : ℝ)-(411149593847/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2271/16384 : ℝ) (4543/32768 : ℝ) (411149593847/500000000000 : ℝ) (63093981803/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0464; no trusted numerical premise.
theorem cover7_leaf0464_exp_radius : (997526779978611633/1000000000000000000 : ℝ) ≤ Real.exp ((-71/3584 : ℝ)/8) ∧ Real.exp ((-71/3584 : ℝ)/8) ≤ (498763389989305817/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-71/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0464_exp_lower : (18361778982507703/20000000000000000 : ℝ) ≤ Real.exp ((-1093900781869/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093900781869/1600000000000 : ℝ)/8) ≤ (918088949125385151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093900781869/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0464_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019008142887/1000000000000 : ℝ) ≤ 4*Real.exp (4543/32768 : ℝ)*Real.exp (-mu (radius 7 (71/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019008142887/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (71/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0464_exp_radius
  have hrNumeric : (196076933229/200000000000 : ℝ) ≤ Real.exp (-71/3584 : ℝ) ∧ Real.exp (-71/3584 : ℝ) ≤ (490192333073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196076933229/200000000000 : ℝ) ≤ (radius 7 (71/512 : ℝ)) ∧ (radius 7 (71/512 : ℝ)) ≤ (490192333073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (71/512 : ℝ)) (196076933229/200000000000 : ℝ) (490192333073/500000000000 : ℝ) (19709364877/100000000000 : ℝ) (24636706097/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (71/512 : ℝ)) (196076933229/200000000000 : ℝ) (490192333073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (71/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196076933229/200000000000 : ℝ) (490192333073/500000000000 : ℝ) (61887020817/62500000000 : ℝ) (990192333073/1000000000000 : ℝ) (495071880171/500000000000 : ℝ) (990143760343/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (71/512 : ℝ)) 1 (61887020817/62500000000 : ℝ) (990192333073/1000000000000 : ℝ) (495071880171/500000000000 : ℝ) (990143760343/1000000000000 : ℝ) (990168046707/1000000000000 : ℝ) (247542011677/250000000000 : ℝ) (990168046409/1000000000000 : ℝ) (990168046411/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (71/512 : ℝ)) 2 (990168046707/1000000000000 : ℝ) (247542011677/250000000000 : ℝ) (990168046409/1000000000000 : ℝ) (990168046411/1000000000000 : ℝ) (495084023279/500000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (71/512 : ℝ)) 3 (495084023279/500000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (71/512 : ℝ)) 4 (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (71/512 : ℝ)) 5 (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (71/512 : ℝ)) 6 (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (71/512 : ℝ)) 7 (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (71/512 : ℝ))) (19709364877/100000000000 : ℝ) (24636706097/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19709364877/100000000000 : ℝ) (24636706097/125000000000 : ℝ) (119709364877/200000000000 : ℝ) (149636706097/250000000000 : ℝ) (443952304611/1000000000000 : ℝ) (443952304619/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 1 (119709364877/200000000000 : ℝ) (149636706097/250000000000 : ℝ) (443952304611/1000000000000 : ℝ) (443952304619/1000000000000 : ℝ) (260624782249/500000000000 : ℝ) (65156195563/125000000000 : ℝ) (64435801639/125000000000 : ℝ) (515486413119/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 2 (260624782249/500000000000 : ℝ) (65156195563/125000000000 : ℝ) (64435801639/125000000000 : ℝ) (515486413119/1000000000000 : ℝ) (103673597761/200000000000 : ℝ) (129591997203/250000000000 : ℝ) (129589994873/250000000000 : ℝ) (518359979499/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 3 (103673597761/200000000000 : ℝ) (129591997203/250000000000 : ℝ) (129589994873/250000000000 : ℝ) (518359979499/1000000000000 : ℝ) (129590996037/250000000000 : ℝ) (129590996039/250000000000 : ℝ) (518363984133/1000000000000 : ℝ) (518363984141/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 4 (129590996037/250000000000 : ℝ) (129590996039/250000000000 : ℝ) (518363984133/1000000000000 : ℝ) (518363984141/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 5 (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 6 (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (71/512 : ℝ))) 7 (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (71/512 : ℝ)) hmem 8 (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (71/512 : ℝ))) hcmem 8 (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (71/512 : ℝ)) (990168046557/1000000000000 : ℝ) (6188550291/6250000000 : ℝ) (25918199207/50000000000 : ℝ) (518363984149/1000000000000 : ℝ) (102791168259/125000000000 : ℝ) (82232934609/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0464_exp_lower
  have heNumeric : (2019008142887/1000000000000 : ℝ)/4 ≤ Real.exp (-1093900781869/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019008142887/1000000000000 : ℝ)/4 ≤ Real.exp ((4543/32768 : ℝ)-(82232934609/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4543/32768 : ℝ) (71/512 : ℝ) (82232934609/100000000000 : ℝ) (2019008142887/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0465; no trusted numerical premise.
theorem cover7_leaf0465_exp_radius : (997526236369805473/1000000000000000000 : ℝ) ≤ Real.exp ((-4545/229376 : ℝ)/8) ∧ Real.exp ((-4545/229376 : ℝ)/8) ≤ (498763118184902737/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4545/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0465_exp_lower : (183617798170577493/200000000000000000 : ℝ) ≤ Real.exp ((-136737525013/200000000000 : ℝ)/8) ∧ Real.exp ((-136737525013/200000000000 : ℝ)/8) ≤ (459044495426443733/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136737525013/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0465_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801775401/200000000000 : ℝ) ≤ 4*Real.exp (71/512 : ℝ)*Real.exp (-mu (radius 7 (4545/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403801775401/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4545/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0465_exp_radius
  have hrNumeric : (61273774501/62500000000 : ℝ) ≤ Real.exp (-4545/229376 : ℝ) ∧ Real.exp (-4545/229376 : ℝ) ≤ (980380392017/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61273774501/62500000000 : ℝ) ≤ (radius 7 (4545/32768 : ℝ)) ∧ (radius 7 (4545/32768 : ℝ)) ≤ (980380392017/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4545/32768 : ℝ)) (61273774501/62500000000 : ℝ) (980380392017/1000000000000 : ℝ) (197114907981/1000000000000 : ℝ) (197114907987/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4545/32768 : ℝ)) (61273774501/62500000000 : ℝ) (980380392017/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61273774501/62500000000 : ℝ) (980380392017/1000000000000 : ℝ) (123773774501/125000000000 : ℝ) (990190196009/1000000000000 : ℝ) (495070801001/500000000000 : ℝ) (990141602003/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 1 (123773774501/125000000000 : ℝ) (990190196009/1000000000000 : ℝ) (495070801001/500000000000 : ℝ) (990141602003/1000000000000 : ℝ) (198033179801/200000000000 : ℝ) (495082949503/500000000000 : ℝ) (495082949353/500000000000 : ℝ) (247541474677/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 2 (198033179801/200000000000 : ℝ) (495082949503/500000000000 : ℝ) (495082949353/500000000000 : ℝ) (247541474677/250000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 3 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 4 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 5 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 6 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4545/32768 : ℝ)) 7 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4545/32768 : ℝ))) (197114907981/1000000000000 : ℝ) (197114907987/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197114907981/1000000000000 : ℝ) (197114907987/1000000000000 : ℝ) (59855745399/100000000000 : ℝ) (299278726997/500000000000 : ℝ) (44397624709/100000000000 : ℝ) (221988123549/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 1 (59855745399/100000000000 : ℝ) (299278726997/500000000000 : ℝ) (44397624709/100000000000 : ℝ) (221988123549/500000000000 : ℝ) (26063342527/50000000000 : ℝ) (260633425273/500000000000 : ℝ) (515504890461/1000000000000 : ℝ) (515504890469/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 2 (26063342527/50000000000 : ℝ) (260633425273/500000000000 : ℝ) (515504890461/1000000000000 : ℝ) (515504890469/1000000000000 : ℝ) (1036771741/2000000000 : ℝ) (129596467627/250000000000 : ℝ) (259188932387/500000000000 : ℝ) (259188932391/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 3 (1036771741/2000000000 : ℝ) (129596467627/250000000000 : ℝ) (259188932387/500000000000 : ℝ) (259188932391/500000000000 : ℝ) (518381867637/1000000000000 : ℝ) (103676373529/200000000000 : ℝ) (518381867621/1000000000000 : ℝ) (51838186763/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 4 (518381867637/1000000000000 : ℝ) (103676373529/200000000000 : ℝ) (518381867621/1000000000000 : ℝ) (51838186763/100000000000 : ℝ) (518381867629/1000000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 5 (518381867629/1000000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 6 (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4545/32768 : ℝ))) 7 (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4545/32768 : ℝ)) hmem 8 (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4545/32768 : ℝ))) hcmem 8 (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4545/32768 : ℝ)) (198033179771/200000000000 : ℝ) (990165898857/1000000000000 : ℝ) (129595466907/250000000000 : ℝ) (259190933819/500000000000 : ℝ) (411179750023/500000000000 : ℝ) (164471900013/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0465_exp_lower
  have heNumeric : (403801775401/200000000000 : ℝ)/4 ≤ Real.exp (-136737525013/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801775401/200000000000 : ℝ)/4 ≤ Real.exp ((71/512 : ℝ)-(164471900013/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (71/512 : ℝ) (4545/32768 : ℝ) (164471900013/200000000000 : ℝ) (403801775401/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0466; no trusted numerical premise.
theorem cover7_leaf0466_exp_radius : (249381423190323889/250000000000000000 : ℝ) ≤ Real.exp ((-2273/114688 : ℝ)/8) ∧ Real.exp ((-2273/114688 : ℝ)/8) ≤ (997525692761295557/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2273/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0466_exp_lower : (918089033088094911/1000000000000000000 : ℝ) ≤ Real.exp ((-5469498056303/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498056303/8000000000000 : ℝ)/8) ≤ (14345141142001483/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498056303/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0466_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801924011/200000000000 : ℝ) ≤ 4*Real.exp (4545/32768 : ℝ)*Real.exp (-mu (radius 7 (2273/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403801924011/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2273/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0466_exp_radius
  have hrNumeric : (490188058953/500000000000 : ℝ) ≤ Real.exp (-2273/114688 : ℝ) ∧ Real.exp (-2273/114688 : ℝ) ≤ (980376117907/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490188058953/500000000000 : ℝ) ≤ (radius 7 (2273/16384 : ℝ)) ∧ (radius 7 (2273/16384 : ℝ)) ≤ (980376117907/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2273/16384 : ℝ)) (490188058953/500000000000 : ℝ) (980376117907/1000000000000 : ℝ) (24642020589/125000000000 : ℝ) (98568082359/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2273/16384 : ℝ)) (490188058953/500000000000 : ℝ) (980376117907/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490188058953/500000000000 : ℝ) (980376117907/1000000000000 : ℝ) (990188058953/1000000000000 : ℝ) (495094029477/500000000000 : ℝ) (990139443667/1000000000000 : ℝ) (247534860917/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 1 (990188058953/1000000000000 : ℝ) (495094029477/500000000000 : ℝ) (990139443667/1000000000000 : ℝ) (247534860917/250000000000 : ℝ) (99016375131/100000000000 : ℝ) (990163751311/1000000000000 : ℝ) (990163751011/1000000000000 : ℝ) (990163751013/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 2 (99016375131/100000000000 : ℝ) (990163751311/1000000000000 : ℝ) (990163751011/1000000000000 : ℝ) (990163751013/1000000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 3 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 4 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 5 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 6 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2273/16384 : ℝ)) 7 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2273/16384 : ℝ))) (24642020589/125000000000 : ℝ) (98568082359/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24642020589/125000000000 : ℝ) (98568082359/500000000000 : ℝ) (149642020589/250000000000 : ℝ) (598568082359/1000000000000 : ℝ) (222000092743/500000000000 : ℝ) (222000092747/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 1 (149642020589/250000000000 : ℝ) (598568082359/1000000000000 : ℝ) (222000092743/500000000000 : ℝ) (222000092747/500000000000 : ℝ) (521284133921/1000000000000 : ℝ) (521284133927/1000000000000 : ℝ) (515523364739/1000000000000 : ℝ) (257761682373/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 2 (521284133921/1000000000000 : ℝ) (521284133927/1000000000000 : ℝ) (515523364739/1000000000000 : ℝ) (257761682373/500000000000 : ℝ) (51840374933/100000000000 : ℝ) (518403749337/1000000000000 : ℝ) (518395747189/1000000000000 : ℝ) (129598936799/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 3 (51840374933/100000000000 : ℝ) (518403749337/1000000000000 : ℝ) (518395747189/1000000000000 : ℝ) (129598936799/250000000000 : ℝ) (518399748259/1000000000000 : ℝ) (518399748267/1000000000000 : ℝ) (129599937061/250000000000 : ℝ) (129599937063/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 4 (518399748259/1000000000000 : ℝ) (518399748267/1000000000000 : ℝ) (129599937061/250000000000 : ℝ) (129599937063/250000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 5 (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 6 (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2273/16384 : ℝ))) 7 (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2273/16384 : ℝ)) hmem 8 (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2273/16384 : ℝ))) hcmem 8 (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2273/16384 : ℝ)) (24754093779/25000000000 : ℝ) (495081875581/500000000000 : ℝ) (518399748251/1000000000000 : ℝ) (25919987413/50000000000 : ℝ) (822389649599/1000000000000 : ℝ) (51399353101/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0466_exp_lower
  have heNumeric : (403801924011/200000000000 : ℝ)/4 ≤ Real.exp (-5469498056303/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801924011/200000000000 : ℝ)/4 ≤ Real.exp ((4545/32768 : ℝ)-(51399353101/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4545/32768 : ℝ) (2273/16384 : ℝ) (51399353101/62500000000 : ℝ) (403801924011/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0467; no trusted numerical premise.
theorem cover7_leaf0467_exp_radius : (498762574576540941/500000000000000000 : ℝ) ≤ Real.exp ((-4547/229376 : ℝ)/8) ∧ Real.exp ((-4547/229376 : ℝ)/8) ≤ (997525149153081883/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4547/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0467_exp_lower : (918089075831237081/1000000000000000000 : ℝ) ≤ Real.exp ((-2734747538339/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734747538339/4000000000000 : ℝ)/8) ≤ (459044537915618541/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734747538339/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0467_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505186021/500000000000 : ℝ) ≤ 4*Real.exp (2273/16384 : ℝ)*Real.exp (-mu (radius 7 (4547/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505186021/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4547/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0467_exp_radius
  have hrNumeric : (196074368763/200000000000 : ℝ) ≤ Real.exp (-4547/229376 : ℝ) ∧ Real.exp (-4547/229376 : ℝ) ≤ (122546480477/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196074368763/200000000000 : ℝ) ≤ (radius 7 (4547/32768 : ℝ)) ∧ (radius 7 (4547/32768 : ℝ)) ≤ (122546480477/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4547/32768 : ℝ)) (196074368763/200000000000 : ℝ) (122546480477/125000000000 : ℝ) (49289354741/250000000000 : ℝ) (19715741897/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4547/32768 : ℝ)) (196074368763/200000000000 : ℝ) (122546480477/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196074368763/200000000000 : ℝ) (122546480477/125000000000 : ℝ) (990185921907/1000000000000 : ℝ) (247546480477/250000000000 : ℝ) (990137285337/1000000000000 : ℝ) (495068642669/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 1 (990185921907/1000000000000 : ℝ) (247546480477/250000000000 : ℝ) (990137285337/1000000000000 : ℝ) (495068642669/500000000000 : ℝ) (495080801811/500000000000 : ℝ) (990161603623/1000000000000 : ℝ) (990161603323/1000000000000 : ℝ) (39606464133/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 2 (495080801811/500000000000 : ℝ) (990161603623/1000000000000 : ℝ) (990161603323/1000000000000 : ℝ) (39606464133/40000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 3 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 4 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 5 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 6 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4547/32768 : ℝ)) 7 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4547/32768 : ℝ))) (49289354741/250000000000 : ℝ) (19715741897/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49289354741/250000000000 : ℝ) (19715741897/100000000000 : ℝ) (299289354741/500000000000 : ℝ) (119715741897/200000000000 : ℝ) (444024119799/1000000000000 : ℝ) (444024119807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 1 (299289354741/500000000000 : ℝ) (119715741897/200000000000 : ℝ) (444024119799/1000000000000 : ℝ) (444024119807/1000000000000 : ℝ) (6516267683/12500000000 : ℝ) (260650707323/500000000000 : ℝ) (515541835943/1000000000000 : ℝ) (10310836719/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 2 (6516267683/12500000000 : ℝ) (260650707323/500000000000 : ℝ) (515541835943/1000000000000 : ℝ) (10310836719/20000000000 : ℝ) (518421625291/1000000000000 : ℝ) (259210812649/500000000000 : ℝ) (518413626733/1000000000000 : ℝ) (518413626741/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 3 (518421625291/1000000000000 : ℝ) (259210812649/500000000000 : ℝ) (518413626733/1000000000000 : ℝ) (518413626741/1000000000000 : ℝ) (129604406503/250000000000 : ℝ) (25920881301/50000000000 : ℝ) (129604406499/250000000000 : ℝ) (103683525201/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 4 (129604406503/250000000000 : ℝ) (25920881301/50000000000 : ℝ) (129604406499/250000000000 : ℝ) (103683525201/200000000000 : ℝ) (129604406501/250000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 5 (129604406501/250000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 6 (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4547/32768 : ℝ))) 7 (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4547/32768 : ℝ)) hmem 8 (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4547/32768 : ℝ))) hcmem 8 (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4547/32768 : ℝ)) (61885100217/62500000000 : ℝ) (495080801737/500000000000 : ℝ) (518417626003/1000000000000 : ℝ) (518417626013/1000000000000 : ℝ) (411209897361/500000000000 : ℝ) (822419794741/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0467_exp_lower
  have heNumeric : (1009505186021/500000000000 : ℝ)/4 ≤ Real.exp (-2734747538339/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505186021/500000000000 : ℝ)/4 ≤ Real.exp ((2273/16384 : ℝ)-(822419794741/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2273/16384 : ℝ) (4547/32768 : ℝ) (822419794741/1000000000000 : ℝ) (1009505186021/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0468; no trusted numerical premise.
theorem cover7_leaf0468_exp_radius : (997524605545164451/1000000000000000000 : ℝ) ≤ Real.exp ((-1137/57344 : ℝ)/8) ∧ Real.exp ((-1137/57344 : ℝ)/8) ≤ (249381151386291113/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1137/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0468_exp_lower : (918089119080936913/1000000000000000000 : ℝ) ≤ Real.exp ((-5469492061741/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469492061741/8000000000000 : ℝ)/8) ≤ (459044559540468457/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469492061741/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0468_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011132941/1000000000000 : ℝ) ≤ 4*Real.exp (4547/32768 : ℝ)*Real.exp (-mu (radius 7 (1137/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011132941/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1137/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0468_exp_radius
  have hrNumeric : (490183784871/500000000000 : ℝ) ≤ Real.exp (-1137/57344 : ℝ) ∧ Real.exp (-1137/57344 : ℝ) ≤ (980367569743/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490183784871/500000000000 : ℝ) ≤ (radius 7 (1137/8192 : ℝ)) ∧ (radius 7 (1137/8192 : ℝ)) ≤ (980367569743/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1137/8192 : ℝ)) (490183784871/500000000000 : ℝ) (980367569743/1000000000000 : ℝ) (197178670743/1000000000000 : ℝ) (197178670749/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1137/8192 : ℝ)) (490183784871/500000000000 : ℝ) (980367569743/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490183784871/500000000000 : ℝ) (980367569743/1000000000000 : ℝ) (990183784871/1000000000000 : ℝ) (123772973109/125000000000 : ℝ) (990135127011/1000000000000 : ℝ) (247533781753/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 1 (990183784871/1000000000000 : ℝ) (123772973109/125000000000 : ℝ) (990135127011/1000000000000 : ℝ) (247533781753/250000000000 : ℝ) (990159455941/1000000000000 : ℝ) (495079727971/500000000000 : ℝ) (495079727821/500000000000 : ℝ) (247539863911/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 2 (990159455941/1000000000000 : ℝ) (495079727971/500000000000 : ℝ) (495079727821/500000000000 : ℝ) (247539863911/250000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 3 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 4 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 5 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 6 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1137/8192 : ℝ)) 7 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1137/8192 : ℝ))) (197178670743/1000000000000 : ℝ) (197178670749/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197178670743/1000000000000 : ℝ) (197178670749/1000000000000 : ℝ) (598589335371/1000000000000 : ℝ) (4788714683/8000000000 : ℝ) (222024025019/500000000000 : ℝ) (222024025023/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 1 (598589335371/1000000000000 : ℝ) (4788714683/8000000000 : ℝ) (222024025019/500000000000 : ℝ) (222024025023/500000000000 : ℝ) (16291209147/31250000000 : ℝ) (521318692711/1000000000000 : ℝ) (515560304081/1000000000000 : ℝ) (515560304089/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 2 (16291209147/31250000000 : ℝ) (521318692711/1000000000000 : ℝ) (515560304081/1000000000000 : ℝ) (515560304089/1000000000000 : ℝ) (64804937299/125000000000 : ℝ) (648049373/1250000000 : ℝ) (103686300683/200000000000 : ℝ) (518431503423/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 3 (64804937299/125000000000 : ℝ) (648049373/1250000000 : ℝ) (103686300683/200000000000 : ℝ) (518431503423/1000000000000 : ℝ) (518435500903/1000000000000 : ℝ) (32402218807/62500000000 : ℝ) (64804437611/125000000000 : ℝ) (518435500897/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 4 (518435500903/1000000000000 : ℝ) (32402218807/62500000000 : ℝ) (64804437611/125000000000 : ℝ) (518435500897/1000000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 5 (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 6 (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1137/8192 : ℝ))) 7 (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1137/8192 : ℝ)) hmem 8 (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1137/8192 : ℝ))) hcmem 8 (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1137/8192 : ℝ)) (990159455791/1000000000000 : ℝ) (990159455793/1000000000000 : ℝ) (103687100179/200000000000 : ℝ) (103687100181/200000000000 : ℝ) (822449935433/1000000000000 : ℝ) (205612483863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0468_exp_lower
  have heNumeric : (2019011132941/1000000000000 : ℝ)/4 ≤ Real.exp (-5469492061741/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011132941/1000000000000 : ℝ)/4 ≤ Real.exp ((4547/32768 : ℝ)-(205612483863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4547/32768 : ℝ) (1137/8192 : ℝ) (205612483863/250000000000 : ℝ) (2019011132941/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0469; no trusted numerical premise.
theorem cover7_leaf0469_exp_radius : (997524061937543263/1000000000000000000 : ℝ) ≤ Real.exp ((-4549/229376 : ℝ)/8) ∧ Real.exp ((-4549/229376 : ℝ)/8) ≤ (31172626935548227/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4549/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0469_exp_lower : (183617832567599561/200000000000000000 : ℝ) ≤ Real.exp ((-1367372252859/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367372252859/2000000000000 : ℝ)/8) ≤ (459044581418998903/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367372252859/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0469_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505951383/500000000000 : ℝ) ≤ 4*Real.exp (1137/8192 : ℝ)*Real.exp (-mu (radius 7 (4549/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505951383/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4549/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0469_exp_radius
  have hrNumeric : (122545411961/125000000000 : ℝ) ≤ Real.exp (-4549/229376 : ℝ) ∧ Real.exp (-4549/229376 : ℝ) ≤ (980363295689/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122545411961/125000000000 : ℝ) ≤ (radius 7 (4549/32768 : ℝ)) ∧ (radius 7 (4549/32768 : ℝ)) ≤ (980363295689/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4549/32768 : ℝ)) (122545411961/125000000000 : ℝ) (980363295689/1000000000000 : ℝ) (39439984009/200000000000 : ℝ) (197199920051/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4549/32768 : ℝ)) (122545411961/125000000000 : ℝ) (980363295689/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122545411961/125000000000 : ℝ) (980363295689/1000000000000 : ℝ) (247545411961/250000000000 : ℝ) (198036329569/200000000000 : ℝ) (99013296869/100000000000 : ℝ) (247533242173/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 1 (247545411961/250000000000 : ℝ) (198036329569/200000000000 : ℝ) (99013296869/100000000000 : ℝ) (247533242173/250000000000 : ℝ) (990157308267/1000000000000 : ℝ) (990157308269/1000000000000 : ℝ) (990157307967/1000000000000 : ℝ) (99015730797/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 2 (990157308267/1000000000000 : ℝ) (990157308269/1000000000000 : ℝ) (990157307967/1000000000000 : ℝ) (99015730797/100000000000 : ℝ) (990157308117/1000000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 3 (990157308117/1000000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 4 (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 5 (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 6 (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4549/32768 : ℝ)) 7 (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4549/32768 : ℝ))) (39439984009/200000000000 : ℝ) (197199920051/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39439984009/200000000000 : ℝ) (197199920051/1000000000000 : ℝ) (299299980011/500000000000 : ℝ) (299299980013/500000000000 : ℝ) (222035988099/500000000000 : ℝ) (222035988103/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 1 (299299980011/500000000000 : ℝ) (299299980013/500000000000 : ℝ) (222035988099/500000000000 : ℝ) (222035988103/500000000000 : ℝ) (52133596811/100000000000 : ℝ) (130333992029/250000000000 : ℝ) (10311575383/20000000000 : ℝ) (257789384579/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 2 (52133596811/100000000000 : ℝ) (130333992029/250000000000 : ℝ) (10311575383/20000000000 : ℝ) (257789384579/500000000000 : ℝ) (51845736863/100000000000 : ℝ) (518457368637/1000000000000 : ℝ) (518449377231/1000000000000 : ℝ) (518449377239/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 3 (51845736863/100000000000 : ℝ) (518457368637/1000000000000 : ℝ) (518449377231/1000000000000 : ℝ) (518449377239/1000000000000 : ℝ) (51845337293/100000000000 : ℝ) (259226686469/500000000000 : ℝ) (103690674583/200000000000 : ℝ) (518453372923/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 4 (51845337293/100000000000 : ℝ) (259226686469/500000000000 : ℝ) (103690674583/200000000000 : ℝ) (518453372923/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 5 (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 6 (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4549/32768 : ℝ))) 7 (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4549/32768 : ℝ)) hmem 8 (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4549/32768 : ℝ))) hcmem 8 (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4549/32768 : ℝ)) (247539327029/250000000000 : ℝ) (24753932703/25000000000 : ℝ) (259226686461/500000000000 : ℝ) (518453372931/1000000000000 : ℝ) (822480071723/1000000000000 : ℝ) (411240035871/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0469_exp_lower
  have heNumeric : (1009505951383/500000000000 : ℝ)/4 ≤ Real.exp (-1367372252859/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505951383/500000000000 : ℝ)/4 ≤ Real.exp ((1137/8192 : ℝ)-(411240035871/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1137/8192 : ℝ) (4549/32768 : ℝ) (411240035871/500000000000 : ℝ) (1009505951383/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0470; no trusted numerical premise.
theorem cover7_leaf0470_exp_radius : (997523518330218317/1000000000000000000 : ℝ) ≤ Real.exp ((-325/16384 : ℝ)/8) ∧ Real.exp ((-325/16384 : ℝ)/8) ≤ (498761759165109159/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-325/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0470_exp_lower : (918089207102190309/1000000000000000000 : ℝ) ≤ Real.exp ((-5469485925779/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469485925779/8000000000000 : ℝ)/8) ≤ (91808920710219031/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469485925779/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0470_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012681513/1000000000000 : ℝ) ≤ 4*Real.exp (4549/32768 : ℝ)*Real.exp (-mu (radius 7 (2275/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012681513/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2275/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0470_exp_radius
  have hrNumeric : (980359021653/1000000000000 : ℝ) ≤ Real.exp (-325/16384 : ℝ) ∧ Real.exp (-325/16384 : ℝ) ≤ (490179510827/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980359021653/1000000000000 : ℝ) ≤ (radius 7 (2275/16384 : ℝ)) ∧ (radius 7 (2275/16384 : ℝ)) ≤ (490179510827/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2275/16384 : ℝ)) (980359021653/1000000000000 : ℝ) (490179510827/500000000000 : ℝ) (19722116687/100000000000 : ℝ) (49305291719/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2275/16384 : ℝ)) (980359021653/1000000000000 : ℝ) (490179510827/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980359021653/1000000000000 : ℝ) (490179510827/500000000000 : ℝ) (495089755413/500000000000 : ℝ) (990179510827/1000000000000 : ℝ) (495065405187/500000000000 : ℝ) (123766351297/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 1 (495089755413/500000000000 : ℝ) (990179510827/1000000000000 : ℝ) (495065405187/500000000000 : ℝ) (123766351297/125000000000 : ℝ) (4950775803/5000000000 : ℝ) (495077580301/500000000000 : ℝ) (9901551603/10000000000 : ℝ) (990155160303/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 2 (4950775803/5000000000 : ℝ) (495077580301/500000000000 : ℝ) (9901551603/10000000000 : ℝ) (990155160303/1000000000000 : ℝ) (19803103209/20000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 3 (19803103209/20000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 4 (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 5 (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 6 (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2275/16384 : ℝ)) 7 (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2275/16384 : ℝ))) (19722116687/100000000000 : ℝ) (49305291719/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19722116687/100000000000 : ℝ) (49305291719/250000000000 : ℝ) (119722116687/200000000000 : ℝ) (299305291719/500000000000 : ℝ) (11102397457/25000000000 : ℝ) (27755993643/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 1 (119722116687/200000000000 : ℝ) (299305291719/500000000000 : ℝ) (11102397457/25000000000 : ℝ) (27755993643/62500000000 : ℝ) (521353240857/1000000000000 : ℝ) (521353240863/1000000000000 : ℝ) (10311944623/20000000000 : ℝ) (515597231157/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 2 (521353240857/1000000000000 : ℝ) (521353240863/1000000000000 : ℝ) (10311944623/20000000000 : ℝ) (515597231157/1000000000000 : ℝ) (518475236003/1000000000000 : ℝ) (51847523601/100000000000 : ℝ) (518467248181/1000000000000 : ℝ) (518467248189/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 3 (518475236003/1000000000000 : ℝ) (51847523601/100000000000 : ℝ) (518467248181/1000000000000 : ℝ) (518467248189/1000000000000 : ℝ) (129617810523/250000000000 : ℝ) (5184712421/10000000000 : ℝ) (129617810519/250000000000 : ℝ) (103694248417/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 4 (129617810523/250000000000 : ℝ) (5184712421/10000000000 : ℝ) (129617810519/250000000000 : ℝ) (103694248417/200000000000 : ℝ) (129617810521/250000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 5 (129617810521/250000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 6 (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2275/16384 : ℝ))) 7 (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2275/16384 : ℝ)) hmem 8 (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2275/16384 : ℝ))) hcmem 8 (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2275/16384 : ℝ)) (990155160449/1000000000000 : ℝ) (990155160453/1000000000000 : ℝ) (518471242083/1000000000000 : ℝ) (518471242093/1000000000000 : ℝ) (102813775449/125000000000 : ℝ) (822510203613/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0470_exp_lower
  have heNumeric : (2019012681513/1000000000000 : ℝ)/4 ≤ Real.exp (-5469485925779/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012681513/1000000000000 : ℝ)/4 ≤ Real.exp ((4549/32768 : ℝ)-(822510203613/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4549/32768 : ℝ) (2275/16384 : ℝ) (822510203613/1000000000000 : ℝ) (2019012681513/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0471; no trusted numerical premise.
theorem cover7_leaf0471_exp_radius : (498761487361594807/500000000000000000 : ℝ) ≤ Real.exp ((-4551/229376 : ℝ)/8) ∧ Real.exp ((-4551/229376 : ℝ)/8) ≤ (199504594944637923/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4551/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0471_exp_lower : (114761156484074551/125000000000000000 : ℝ) ≤ Real.exp ((-2734741402417/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734741402417/4000000000000 : ℝ)/8) ≤ (918089251872596409/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734741402417/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0471_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013469167/1000000000000 : ℝ) ≤ 4*Real.exp (2275/16384 : ℝ)*Real.exp (-mu (radius 7 (4551/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013469167/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4551/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0471_exp_radius
  have hrNumeric : (245088686909/250000000000 : ℝ) ≤ Real.exp (-4551/229376 : ℝ) ∧ Real.exp (-4551/229376 : ℝ) ≤ (980354747637/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245088686909/250000000000 : ℝ) ≤ (radius 7 (4551/32768 : ℝ)) ∧ (radius 7 (4551/32768 : ℝ)) ≤ (980354747637/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4551/32768 : ℝ)) (245088686909/250000000000 : ℝ) (980354747637/1000000000000 : ℝ) (24655301403/125000000000 : ℝ) (19724241123/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4551/32768 : ℝ)) (245088686909/250000000000 : ℝ) (980354747637/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245088686909/250000000000 : ℝ) (980354747637/1000000000000 : ℝ) (495088686909/500000000000 : ℝ) (990177373819/1000000000000 : ℝ) (495064326031/500000000000 : ℝ) (30941520377/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 1 (495088686909/500000000000 : ℝ) (990177373819/1000000000000 : ℝ) (495064326031/500000000000 : ℝ) (30941520377/31250000000 : ℝ) (49507650647/50000000000 : ℝ) (495076506471/500000000000 : ℝ) (6188456329/6250000000 : ℝ) (495076506321/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 2 (49507650647/50000000000 : ℝ) (495076506471/500000000000 : ℝ) (6188456329/6250000000 : ℝ) (495076506321/500000000000 : ℝ) (99015301279/100000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 3 (99015301279/100000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 4 (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 5 (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 6 (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4551/32768 : ℝ)) 7 (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4551/32768 : ℝ))) (24655301403/125000000000 : ℝ) (19724241123/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24655301403/125000000000 : ℝ) (19724241123/100000000000 : ℝ) (149655301403/250000000000 : ℝ) (119724241123/200000000000 : ℝ) (111029954073/250000000000 : ℝ) (4441198163/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 1 (149655301403/250000000000 : ℝ) (119724241123/200000000000 : ℝ) (111029954073/250000000000 : ℝ) (4441198163/10000000000 : ℝ) (65171313869/125000000000 : ℝ) (260685255479/500000000000 : ℝ) (515615690087/1000000000000 : ℝ) (257807845047/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 2 (65171313869/125000000000 : ℝ) (260685255479/500000000000 : ℝ) (515615690087/1000000000000 : ℝ) (257807845047/500000000000 : ℝ) (518493100519/1000000000000 : ℝ) (259246550263/500000000000 : ℝ) (518485116271/1000000000000 : ℝ) (518485116279/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 3 (518493100519/1000000000000 : ℝ) (259246550263/500000000000 : ℝ) (518485116271/1000000000000 : ℝ) (518485116279/1000000000000 : ℝ) (103697821679/200000000000 : ℝ) (518489108403/1000000000000 : ℝ) (518489108379/1000000000000 : ℝ) (129622277097/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 4 (103697821679/200000000000 : ℝ) (518489108403/1000000000000 : ℝ) (518489108379/1000000000000 : ℝ) (129622277097/250000000000 : ℝ) (518489108387/1000000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 5 (518489108387/1000000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 6 (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4551/32768 : ℝ))) 7 (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4551/32768 : ℝ)) hmem 8 (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4551/32768 : ℝ))) hcmem 8 (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4551/32768 : ℝ)) (990153012789/1000000000000 : ℝ) (123769126599/125000000000 : ℝ) (259244554193/500000000000 : ℝ) (129622277099/250000000000 : ℝ) (822540331053/1000000000000 : ℝ) (822540331073/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0471_exp_lower
  have heNumeric : (2019013469167/1000000000000 : ℝ)/4 ≤ Real.exp (-2734741402417/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013469167/1000000000000 : ℝ)/4 ≤ Real.exp ((2275/16384 : ℝ)-(822540331073/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2275/16384 : ℝ) (4551/32768 : ℝ) (822540331073/1000000000000 : ℝ) (2019013469167/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0472; no trusted numerical premise.
theorem cover7_leaf0472_exp_radius : (997522431116457153/1000000000000000000 : ℝ) ≤ Real.exp ((-569/28672 : ℝ)/8) ∧ Real.exp ((-569/28672 : ℝ)/8) ≤ (498761215558228577/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-569/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0472_exp_lower : (918089297149560459/1000000000000000000 : ℝ) ≤ Real.exp ((-5469479648577/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469479648577/8000000000000 : ℝ)/8) ≤ (45904464857478023/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469479648577/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0472_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014265733/1000000000000 : ℝ) ≤ 4*Real.exp (4551/32768 : ℝ)*Real.exp (-mu (radius 7 (569/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014265733/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (569/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0472_exp_radius
  have hrNumeric : (490175236819/500000000000 : ℝ) ≤ Real.exp (-569/28672 : ℝ) ∧ Real.exp (-569/28672 : ℝ) ≤ (980350473639/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490175236819/500000000000 : ℝ) ≤ (radius 7 (569/4096 : ℝ)) ∧ (radius 7 (569/4096 : ℝ)) ≤ (980350473639/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (569/4096 : ℝ)) (490175236819/500000000000 : ℝ) (980350473639/1000000000000 : ℝ) (197263653103/1000000000000 : ℝ) (197263653109/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (569/4096 : ℝ)) (490175236819/500000000000 : ℝ) (980350473639/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (569/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490175236819/500000000000 : ℝ) (980350473639/1000000000000 : ℝ) (990175236819/1000000000000 : ℝ) (49508761841/50000000000 : ℝ) (247531623439/250000000000 : ℝ) (990126493757/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (569/4096 : ℝ)) 1 (990175236819/1000000000000 : ℝ) (49508761841/50000000000 : ℝ) (247531623439/250000000000 : ℝ) (990126493757/1000000000000 : ℝ) (990150865287/1000000000000 : ℝ) (990150865289/1000000000000 : ℝ) (990150864987/1000000000000 : ℝ) (990150864989/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (569/4096 : ℝ)) 2 (990150865287/1000000000000 : ℝ) (990150865289/1000000000000 : ℝ) (990150864987/1000000000000 : ℝ) (990150864989/1000000000000 : ℝ) (990150865137/1000000000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (569/4096 : ℝ)) 3 (990150865137/1000000000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (569/4096 : ℝ)) 4 (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (569/4096 : ℝ)) 5 (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (569/4096 : ℝ)) 6 (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (569/4096 : ℝ)) 7 (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (569/4096 : ℝ))) (197263653103/1000000000000 : ℝ) (197263653109/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197263653103/1000000000000 : ℝ) (197263653109/1000000000000 : ℝ) (598631826551/1000000000000 : ℝ) (119726365311/200000000000 : ℝ) (44414373023/100000000000 : ℝ) (222071865119/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 1 (598631826551/1000000000000 : ℝ) (119726365311/200000000000 : ℝ) (44414373023/100000000000 : ℝ) (222071865119/500000000000 : ℝ) (52138777839/100000000000 : ℝ) (521387778397/1000000000000 : ℝ) (257817072979/500000000000 : ℝ) (257817072983/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 2 (52138777839/100000000000 : ℝ) (521387778397/1000000000000 : ℝ) (257817072979/500000000000 : ℝ) (257817072983/500000000000 : ℝ) (259255481087/500000000000 : ℝ) (259255481091/500000000000 : ℝ) (259251490749/500000000000 : ℝ) (518502981507/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 3 (259255481087/500000000000 : ℝ) (259255481091/500000000000 : ℝ) (259251490749/500000000000 : ℝ) (518502981507/1000000000000 : ℝ) (129626742959/250000000000 : ℝ) (103701394369/200000000000 : ℝ) (25925348591/50000000000 : ℝ) (51850697183/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 4 (129626742959/250000000000 : ℝ) (103701394369/200000000000 : ℝ) (25925348591/50000000000 : ℝ) (51850697183/100000000000 : ℝ) (129626742957/250000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 5 (129626742957/250000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 6 (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (569/4096 : ℝ))) 7 (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (569/4096 : ℝ)) hmem 8 (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (569/4096 : ℝ))) hcmem 8 (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (569/4096 : ℝ)) (61884429071/62500000000 : ℝ) (990150865139/1000000000000 : ℝ) (518506971827/1000000000000 : ℝ) (259253485919/500000000000 : ℝ) (411285227049/500000000000 : ℝ) (822570454119/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0472_exp_lower
  have heNumeric : (2019014265733/1000000000000 : ℝ)/4 ≤ Real.exp (-5469479648577/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014265733/1000000000000 : ℝ)/4 ≤ Real.exp ((4551/32768 : ℝ)-(822570454119/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4551/32768 : ℝ) (569/4096 : ℝ) (822570454119/1000000000000 : ℝ) (2019014265733/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0473; no trusted numerical premise.
theorem cover7_leaf0473_exp_radius : (498760943755010467/500000000000000000 : ℝ) ≤ Real.exp ((-4553/229376 : ℝ)/8) ∧ Real.exp ((-4553/229376 : ℝ)/8) ≤ (199504377502004187/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4553/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0473_exp_lower : (183617868586547651/200000000000000000 : ℝ) ≤ Real.exp ((-683684557129/1000000000000 : ℝ)/8) ∧ Real.exp ((-683684557129/1000000000000 : ℝ)/8) ≤ (57380583933296141/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683684557129/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0473_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403803014241/200000000000 : ℝ) ≤ 4*Real.exp (569/4096 : ℝ)*Real.exp (-mu (radius 7 (4553/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403803014241/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4553/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0473_exp_radius
  have hrNumeric : (490173099829/500000000000 : ℝ) ≤ Real.exp (-4553/229376 : ℝ) ∧ Real.exp (-4553/229376 : ℝ) ≤ (980346199659/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490173099829/500000000000 : ℝ) ≤ (radius 7 (4553/32768 : ℝ)) ∧ (radius 7 (4553/32768 : ℝ)) ≤ (980346199659/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4553/32768 : ℝ)) (490173099829/500000000000 : ℝ) (980346199659/1000000000000 : ℝ) (197284892513/1000000000000 : ℝ) (197284892519/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4553/32768 : ℝ)) (490173099829/500000000000 : ℝ) (980346199659/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490173099829/500000000000 : ℝ) (980346199659/1000000000000 : ℝ) (990173099829/1000000000000 : ℝ) (99017309983/100000000000 : ℝ) (990124335453/1000000000000 : ℝ) (198024867091/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 1 (990173099829/1000000000000 : ℝ) (99017309983/100000000000 : ℝ) (990124335453/1000000000000 : ℝ) (198024867091/200000000000 : ℝ) (990148717641/1000000000000 : ℝ) (990148717643/1000000000000 : ℝ) (49507435867/50000000000 : ℝ) (990148717343/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 2 (990148717641/1000000000000 : ℝ) (990148717643/1000000000000 : ℝ) (49507435867/50000000000 : ℝ) (990148717343/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 3 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 4 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 5 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 6 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4553/32768 : ℝ)) 7 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4553/32768 : ℝ))) (197284892513/1000000000000 : ℝ) (197284892519/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197284892513/1000000000000 : ℝ) (197284892519/1000000000000 : ℝ) (37415152891/62500000000 : ℝ) (29932122313/50000000000 : ℝ) (444167640101/1000000000000 : ℝ) (111041910027/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 1 (37415152891/62500000000 : ℝ) (29932122313/50000000000 : ℝ) (444167640101/1000000000000 : ℝ) (111041910027/250000000000 : ℝ) (260702521589/500000000000 : ℝ) (32587815199/62500000000 : ℝ) (515652598769/1000000000000 : ℝ) (64456574847/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 2 (260702521589/500000000000 : ℝ) (32587815199/62500000000 : ℝ) (515652598769/1000000000000 : ℝ) (64456574847/125000000000 : ℝ) (518528820973/1000000000000 : ℝ) (25926441049/50000000000 : ℝ) (129630210967/250000000000 : ℝ) (4148166751/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 3 (518528820973/1000000000000 : ℝ) (25926441049/50000000000 : ℝ) (129630210967/250000000000 : ℝ) (4148166751/8000000000 : ℝ) (25926241621/50000000000 : ℝ) (129631208107/250000000000 : ℝ) (103704966481/200000000000 : ℝ) (518524832413/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 4 (25926241621/50000000000 : ℝ) (129631208107/250000000000 : ℝ) (103704966481/200000000000 : ℝ) (518524832413/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 5 (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 6 (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4553/32768 : ℝ))) 7 (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4553/32768 : ℝ)) hmem 8 (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4553/32768 : ℝ))) hcmem 8 (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4553/32768 : ℝ)) (99014871749/100000000000 : ℝ) (990148717493/1000000000000 : ℝ) (129631208103/250000000000 : ℝ) (518524832421/1000000000000 : ℝ) (822600572737/1000000000000 : ℝ) (411300286377/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0473_exp_lower
  have heNumeric : (403803014241/200000000000 : ℝ)/4 ≤ Real.exp (-683684557129/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403803014241/200000000000 : ℝ)/4 ≤ Real.exp ((569/4096 : ℝ)-(411300286377/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (569/4096 : ℝ) (4553/32768 : ℝ) (411300286377/500000000000 : ℝ) (403803014241/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0474; no trusted numerical premise.
theorem cover7_leaf0474_exp_radius : (997521343903880957/1000000000000000000 : ℝ) ≤ Real.exp ((-2277/114688 : ℝ)/8) ∧ Real.exp ((-2277/114688 : ℝ)/8) ≤ (498760671951940479/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2277/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0474_exp_lower : (918089389221785587/1000000000000000000 : ℝ) ≤ Real.exp ((-5469473230223/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469473230223/8000000000000 : ℝ)/8) ≤ (229522347305446397/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469473230223/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0474_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019015885577/1000000000000 : ℝ) ≤ 4*Real.exp (4553/32768 : ℝ)*Real.exp (-mu (radius 7 (2277/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019015885577/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2277/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0474_exp_radius
  have hrNumeric : (980341925697/1000000000000 : ℝ) ≤ Real.exp (-2277/114688 : ℝ) ∧ Real.exp (-2277/114688 : ℝ) ≤ (490170962849/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980341925697/1000000000000 : ℝ) ≤ (radius 7 (2277/16384 : ℝ)) ∧ (radius 7 (2277/16384 : ℝ)) ≤ (490170962849/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2277/16384 : ℝ)) (980341925697/1000000000000 : ℝ) (490170962849/500000000000 : ℝ) (3946122589/20000000000 : ℝ) (12331633091/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2277/16384 : ℝ)) (980341925697/1000000000000 : ℝ) (490170962849/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980341925697/1000000000000 : ℝ) (490170962849/500000000000 : ℝ) (30942842589/31250000000 : ℝ) (990170962849/1000000000000 : ℝ) (247530544289/250000000000 : ℝ) (990122177157/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 1 (30942842589/31250000000 : ℝ) (990170962849/1000000000000 : ℝ) (247530544289/250000000000 : ℝ) (990122177157/1000000000000 : ℝ) (495073285001/500000000000 : ℝ) (990146570003/1000000000000 : ℝ) (990146569701/1000000000000 : ℝ) (990146569703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 2 (495073285001/500000000000 : ℝ) (990146570003/1000000000000 : ℝ) (990146569701/1000000000000 : ℝ) (990146569703/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 3 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 4 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 5 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 6 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2277/16384 : ℝ)) 7 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2277/16384 : ℝ))) (3946122589/20000000000 : ℝ) (12331633091/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3946122589/20000000000 : ℝ) (12331633091/62500000000 : ℝ) (23946122589/40000000000 : ℝ) (74831633091/125000000000 : ℝ) (444191545901/1000000000000 : ℝ) (111047886477/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 1 (23946122589/40000000000 : ℝ) (74831633091/125000000000 : ℝ) (444191545901/1000000000000 : ℝ) (111047886477/250000000000 : ℝ) (521422305313/1000000000000 : ℝ) (260711152659/500000000000 : ℝ) (128917762129/250000000000 : ℝ) (515671048523/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 2 (521422305313/1000000000000 : ℝ) (260711152659/500000000000 : ℝ) (128917762129/250000000000 : ℝ) (515671048523/1000000000000 : ℝ) (259273338457/500000000000 : ℝ) (518546676921/1000000000000 : ℝ) (518538703377/1000000000000 : ℝ) (64817337923/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 3 (259273338457/500000000000 : ℝ) (518546676921/1000000000000 : ℝ) (518538703377/1000000000000 : ℝ) (64817337923/125000000000 : ℝ) (103708538029/200000000000 : ℝ) (518542690153/1000000000000 : ℝ) (51854269013/100000000000 : ℝ) (259271345069/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 4 (103708538029/200000000000 : ℝ) (518542690153/1000000000000 : ℝ) (51854269013/100000000000 : ℝ) (259271345069/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 5 (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 6 (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2277/16384 : ℝ))) 7 (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2277/16384 : ℝ)) hmem 8 (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2277/16384 : ℝ))) hcmem 8 (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2277/16384 : ℝ)) (990146569851/1000000000000 : ℝ) (990146569853/1000000000000 : ℝ) (518542690137/1000000000000 : ℝ) (259271345073/500000000000 : ℝ) (205657671741/250000000000 : ℝ) (822630686981/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0474_exp_lower
  have heNumeric : (2019015885577/1000000000000 : ℝ)/4 ≤ Real.exp (-5469473230223/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019015885577/1000000000000 : ℝ)/4 ≤ Real.exp ((4553/32768 : ℝ)-(822630686981/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4553/32768 : ℝ) (2277/16384 : ℝ) (822630686981/1000000000000 : ℝ) (2019015885577/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0450_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0450_certificate
#check SmaleRate.Proofs.cover7_leaf0451_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0451_certificate
#check SmaleRate.Proofs.cover7_leaf0452_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0452_certificate
#check SmaleRate.Proofs.cover7_leaf0453_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0453_certificate
#check SmaleRate.Proofs.cover7_leaf0454_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0454_certificate
#check SmaleRate.Proofs.cover7_leaf0455_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0455_certificate
#check SmaleRate.Proofs.cover7_leaf0456_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0456_certificate
#check SmaleRate.Proofs.cover7_leaf0457_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0457_certificate
#check SmaleRate.Proofs.cover7_leaf0458_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0458_certificate
#check SmaleRate.Proofs.cover7_leaf0459_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0459_certificate
#check SmaleRate.Proofs.cover7_leaf0460_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0460_certificate
#check SmaleRate.Proofs.cover7_leaf0461_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0461_certificate
#check SmaleRate.Proofs.cover7_leaf0462_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0462_certificate
#check SmaleRate.Proofs.cover7_leaf0463_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0463_certificate
#check SmaleRate.Proofs.cover7_leaf0464_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0464_certificate
#check SmaleRate.Proofs.cover7_leaf0465_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0465_certificate
#check SmaleRate.Proofs.cover7_leaf0466_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0466_certificate
#check SmaleRate.Proofs.cover7_leaf0467_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0467_certificate
#check SmaleRate.Proofs.cover7_leaf0468_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0468_certificate
#check SmaleRate.Proofs.cover7_leaf0469_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0469_certificate
#check SmaleRate.Proofs.cover7_leaf0470_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0470_certificate
#check SmaleRate.Proofs.cover7_leaf0471_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0471_certificate
#check SmaleRate.Proofs.cover7_leaf0472_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0472_certificate
#check SmaleRate.Proofs.cover7_leaf0473_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0473_certificate
#check SmaleRate.Proofs.cover7_leaf0474_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0474_certificate
