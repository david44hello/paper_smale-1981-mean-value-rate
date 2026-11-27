/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0350; no trusted numerical premise.
theorem cover7_leaf0350_exp_radius : (997561299744479077/1000000000000000000 : ℝ) ≤ Real.exp ((-8961/458752 : ℝ)/8) ∧ Real.exp ((-8961/458752 : ℝ)/8) ≤ (498780649872239539/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8961/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0350_exp_lower : (459044549445598141/500000000000000000 : ℝ) ≤ Real.exp ((-341843341823/500000000000 : ℝ)/8) ∧ Real.exp ((-341843341823/500000000000 : ℝ)/8) ≤ (918089098891196283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341843341823/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0350_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010777739/1000000000000 : ℝ) ≤ 4*Real.exp (35/256 : ℝ)*Real.exp (-mu (radius 7 (8961/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010777739/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8961/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0350_exp_radius
  have hrNumeric : (245164027869/250000000000 : ℝ) ≤ Real.exp (-8961/458752 : ℝ) ∧ Real.exp (-8961/458752 : ℝ) ≤ (980656111477/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245164027869/250000000000 : ℝ) ≤ (radius 7 (8961/65536 : ℝ)) ∧ (radius 7 (8961/65536 : ℝ)) ≤ (980656111477/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8961/65536 : ℝ)) (245164027869/250000000000 : ℝ) (980656111477/1000000000000 : ℝ) (195738578269/1000000000000 : ℝ) (7829543131/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8961/65536 : ℝ)) (245164027869/250000000000 : ℝ) (980656111477/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245164027869/250000000000 : ℝ) (980656111477/1000000000000 : ℝ) (495164027869/500000000000 : ℝ) (990328055739/1000000000000 : ℝ) (123785103069/125000000000 : ℝ) (990280824553/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 1 (495164027869/500000000000 : ℝ) (990328055739/1000000000000 : ℝ) (123785103069/125000000000 : ℝ) (990280824553/1000000000000 : ℝ) (198060888029/200000000000 : ℝ) (495152220073/500000000000 : ℝ) (990304439863/1000000000000 : ℝ) (198060887973/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 2 (198060888029/200000000000 : ℝ) (495152220073/500000000000 : ℝ) (990304439863/1000000000000 : ℝ) (198060887973/200000000000 : ℝ) (247576110001/250000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 3 (247576110001/250000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 4 (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 5 (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 6 (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8961/65536 : ℝ)) 7 (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8961/65536 : ℝ))) (195738578269/1000000000000 : ℝ) (7829543131/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195738578269/1000000000000 : ℝ) (7829543131/40000000000 : ℝ) (298934644567/500000000000 : ℝ) (298934644569/500000000000 : ℝ) (442423528159/1000000000000 : ℝ) (442423528167/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 1 (298934644567/500000000000 : ℝ) (298934644569/500000000000 : ℝ) (442423528159/1000000000000 : ℝ) (442423528167/1000000000000 : ℝ) (260073204323/500000000000 : ℝ) (520146408653/1000000000000 : ℝ) (514306756981/1000000000000 : ℝ) (128576689247/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 2 (260073204323/500000000000 : ℝ) (520146408653/1000000000000 : ℝ) (514306756981/1000000000000 : ℝ) (128576689247/250000000000 : ℝ) (517226582813/1000000000000 : ℝ) (517226582821/1000000000000 : ℝ) (129304585327/250000000000 : ℝ) (129304585329/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 3 (517226582813/1000000000000 : ℝ) (517226582821/1000000000000 : ℝ) (129304585327/250000000000 : ℝ) (129304585329/250000000000 : ℝ) (25861123103/50000000000 : ℝ) (517222462069/1000000000000 : ℝ) (129305615511/250000000000 : ℝ) (517222462053/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 4 (25861123103/50000000000 : ℝ) (517222462069/1000000000000 : ℝ) (129305615511/250000000000 : ℝ) (517222462053/1000000000000 : ℝ) (129305615513/250000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 5 (129305615513/250000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 6 (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8961/65536 : ℝ))) 7 (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8961/65536 : ℝ)) hmem 8 (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8961/65536 : ℝ))) hcmem 8 (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8961/65536 : ℝ)) (990304440003/1000000000000 : ℝ) (495152220003/500000000000 : ℝ) (517222462051/1000000000000 : ℝ) (517222462061/1000000000000 : ℝ) (410202716813/500000000000 : ℝ) (410202716823/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0350_exp_lower
  have heNumeric : (2019010777739/1000000000000 : ℝ)/4 ≤ Real.exp (-341843341823/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010777739/1000000000000 : ℝ)/4 ≤ Real.exp ((35/256 : ℝ)-(410202716823/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (35/256 : ℝ) (8961/65536 : ℝ) (410202716823/500000000000 : ℝ) (2019010777739/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0351; no trusted numerical premise.
theorem cover7_leaf0351_exp_radius : (498780513965316539/500000000000000000 : ℝ) ≤ Real.exp ((-4481/229376 : ℝ)/8) ∧ Real.exp ((-4481/229376 : ℝ)/8) ≤ (997561027930633079/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4481/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0351_exp_lower : (918089103371019223/1000000000000000000 : ℝ) ≤ Real.exp ((-10938986313759/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938986313759/16000000000000 : ℝ)/8) ≤ (114761137921377403/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938986313759/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0351_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505428277/500000000000 : ℝ) ≤ 4*Real.exp (8961/65536 : ℝ)*Real.exp (-mu (radius 7 (4481/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505428277/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4481/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0351_exp_radius
  have hrNumeric : (490326986909/500000000000 : ℝ) ≤ Real.exp (-4481/229376 : ℝ) ∧ Real.exp (-4481/229376 : ℝ) ≤ (980653973819/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490326986909/500000000000 : ℝ) ≤ (radius 7 (4481/32768 : ℝ)) ∧ (radius 7 (4481/32768 : ℝ)) ≤ (980653973819/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4481/32768 : ℝ)) (490326986909/500000000000 : ℝ) (980653973819/1000000000000 : ℝ) (97874643847/500000000000 : ℝ) (1957492877/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4481/32768 : ℝ)) (490326986909/500000000000 : ℝ) (980653973819/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490326986909/500000000000 : ℝ) (980653973819/1000000000000 : ℝ) (990326986909/1000000000000 : ℝ) (99032698691/100000000000 : ℝ) (61892484077/62500000000 : ℝ) (495139872617/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 1 (990326986909/1000000000000 : ℝ) (99032698691/100000000000 : ℝ) (61892484077/62500000000 : ℝ) (495139872617/500000000000 : ℝ) (99030336607/100000000000 : ℝ) (123787920759/125000000000 : ℝ) (247575841447/250000000000 : ℝ) (990303365791/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 2 (99030336607/100000000000 : ℝ) (123787920759/125000000000 : ℝ) (247575841447/250000000000 : ℝ) (990303365791/1000000000000 : ℝ) (990303365929/1000000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 3 (990303365929/1000000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 4 (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 5 (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 6 (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4481/32768 : ℝ)) 7 (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4481/32768 : ℝ))) (97874643847/500000000000 : ℝ) (1957492877/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97874643847/500000000000 : ℝ) (1957492877/10000000000 : ℝ) (597874643847/1000000000000 : ℝ) (11957492877/20000000000 : ℝ) (44243563113/100000000000 : ℝ) (221217815569/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 1 (597874643847/1000000000000 : ℝ) (11957492877/20000000000 : ℝ) (44243563113/100000000000 : ℝ) (221217815569/500000000000 : ℝ) (32509696093/62500000000 : ℝ) (260077568747/500000000000 : ℝ) (16072377963/31250000000 : ℝ) (514316094823/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 2 (32509696093/62500000000 : ℝ) (260077568747/500000000000 : ℝ) (16072377963/31250000000 : ℝ) (514316094823/1000000000000 : ℝ) (64654452019/125000000000 : ℝ) (517235616159/1000000000000 : ℝ) (517227376509/1000000000000 : ℝ) (517227376517/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 3 (64654452019/125000000000 : ℝ) (517235616159/1000000000000 : ℝ) (517227376509/1000000000000 : ℝ) (517227376517/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (258615748169/500000000000 : ℝ) (258615748157/500000000000 : ℝ) (258615748161/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 4 (51723149633/100000000000 : ℝ) (258615748169/500000000000 : ℝ) (258615748157/500000000000 : ℝ) (258615748161/500000000000 : ℝ) (258615748161/500000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 5 (258615748161/500000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 6 (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4481/32768 : ℝ))) 7 (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4481/32768 : ℝ)) hmem 8 (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4481/32768 : ℝ))) hcmem 8 (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4481/32768 : ℝ)) (123787920741/125000000000 : ℝ) (247575841483/250000000000 : ℝ) (517231496321/1000000000000 : ℝ) (51723149633/100000000000 : ℝ) (820420653381/1000000000000 : ℝ) (820420653399/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0351_exp_lower
  have heNumeric : (1009505428277/500000000000 : ℝ)/4 ≤ Real.exp (-10938986313759/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505428277/500000000000 : ℝ)/4 ≤ Real.exp ((8961/65536 : ℝ)-(820420653399/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8961/65536 : ℝ) (4481/32768 : ℝ) (820420653399/1000000000000 : ℝ) (1009505428277/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0352; no trusted numerical premise.
theorem cover7_leaf0352_exp_radius : (498780378058430571/500000000000000000 : ℝ) ≤ Real.exp ((-8963/458752 : ℝ)/8) ∧ Real.exp ((-8963/458752 : ℝ)/8) ≤ (997560756116861143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8963/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0352_exp_lower : (918089107979948467/1000000000000000000 : ℝ) ≤ Real.exp ((-5469492835591/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469492835591/8000000000000 : ℝ)/8) ≤ (229522276994987117/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469492835591/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0352_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010937639/1000000000000 : ℝ) ≤ 4*Real.exp (4481/32768 : ℝ)*Real.exp (-mu (radius 7 (8963/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010937639/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8963/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0352_exp_radius
  have hrNumeric : (245162959041/250000000000 : ℝ) ≤ Real.exp (-8963/458752 : ℝ) ∧ Real.exp (-8963/458752 : ℝ) ≤ (196130367233/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245162959041/250000000000 : ℝ) ≤ (radius 7 (8963/65536 : ℝ)) ∧ (radius 7 (8963/65536 : ℝ)) ≤ (196130367233/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8963/65536 : ℝ)) (245162959041/250000000000 : ℝ) (196130367233/200000000000 : ℝ) (195759996491/1000000000000 : ℝ) (195759996497/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8963/65536 : ℝ)) (245162959041/250000000000 : ℝ) (196130367233/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245162959041/250000000000 : ℝ) (196130367233/200000000000 : ℝ) (495162959041/500000000000 : ℝ) (990325918083/1000000000000 : ℝ) (990278665913/1000000000000 : ℝ) (198055733183/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 1 (495162959041/500000000000 : ℝ) (990325918083/1000000000000 : ℝ) (990278665913/1000000000000 : ℝ) (198055733183/200000000000 : ℝ) (990302291997/1000000000000 : ℝ) (990302291999/1000000000000 : ℝ) (198060458343/200000000000 : ℝ) (495151145859/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 2 (990302291997/1000000000000 : ℝ) (990302291999/1000000000000 : ℝ) (198060458343/200000000000 : ℝ) (495151145859/500000000000 : ℝ) (61893893241/62500000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 3 (61893893241/62500000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 4 (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 5 (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 6 (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8963/65536 : ℝ)) 7 (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8963/65536 : ℝ))) (195759996491/1000000000000 : ℝ) (195759996497/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195759996491/1000000000000 : ℝ) (195759996497/1000000000000 : ℝ) (119575999649/200000000000 : ℝ) (597879998249/1000000000000 : ℝ) (442447733061/1000000000000 : ℝ) (110611933267/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 1 (119575999649/200000000000 : ℝ) (597879998249/1000000000000 : ℝ) (442447733061/1000000000000 : ℝ) (110611933267/250000000000 : ℝ) (520163865653/1000000000000 : ℝ) (520163865659/1000000000000 : ℝ) (514325431867/1000000000000 : ℝ) (257162715937/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 2 (520163865653/1000000000000 : ℝ) (520163865659/1000000000000 : ℝ) (514325431867/1000000000000 : ℝ) (257162715937/500000000000 : ℝ) (12931116219/25000000000 : ℝ) (517244648767/1000000000000 : ℝ) (25861820549/50000000000 : ℝ) (517236410987/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 3 (12931116219/25000000000 : ℝ) (517244648767/1000000000000 : ℝ) (25861820549/50000000000 : ℝ) (517236410987/1000000000000 : ℝ) (51724052987/100000000000 : ℝ) (517240529877/1000000000000 : ℝ) (517240529853/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 4 (51724052987/100000000000 : ℝ) (517240529877/1000000000000 : ℝ) (517240529853/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 5 (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 6 (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8963/65536 : ℝ))) 7 (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8963/65536 : ℝ)) hmem 8 (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8963/65536 : ℝ))) hcmem 8 (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8963/65536 : ℝ)) (198060458371/200000000000 : ℝ) (990302291859/1000000000000 : ℝ) (517240529861/1000000000000 : ℝ) (517240529869/1000000000000 : ℝ) (82043587201/100000000000 : ℝ) (820435872027/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0352_exp_lower
  have heNumeric : (2019010937639/1000000000000 : ℝ)/4 ≤ Real.exp (-5469492835591/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010937639/1000000000000 : ℝ)/4 ≤ Real.exp ((4481/32768 : ℝ)-(820435872027/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4481/32768 : ℝ) (8963/65536 : ℝ) (820435872027/1000000000000 : ℝ) (2019010937639/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0353; no trusted numerical premise.
theorem cover7_leaf0353_exp_radius : (99756048430316327/100000000000000000 : ℝ) ≤ Real.exp ((-2241/114688 : ℝ)/8) ∧ Real.exp ((-2241/114688 : ℝ)/8) ≤ (997560484303163271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2241/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0353_exp_lower : (57380569544974417/62500000000000000 : ℝ) ≤ Real.exp ((-10938985010381/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938985010381/16000000000000 : ℝ)/8) ≤ (918089112719590673/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938985010381/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0353_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80760440841/40000000000 : ℝ) ≤ 4*Real.exp (8963/65536 : ℝ)*Real.exp (-mu (radius 7 (2241/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (80760440841/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2241/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0353_exp_radius
  have hrNumeric : (196129939703/200000000000 : ℝ) ≤ Real.exp (-2241/114688 : ℝ) ∧ Real.exp (-2241/114688 : ℝ) ≤ (245162424629/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196129939703/200000000000 : ℝ) ≤ (radius 7 (2241/16384 : ℝ)) ∧ (radius 7 (2241/16384 : ℝ)) ≤ (245162424629/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2241/16384 : ℝ)) (196129939703/200000000000 : ℝ) (245162424629/250000000000 : ℝ) (195770704653/1000000000000 : ℝ) (195770704659/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2241/16384 : ℝ)) (196129939703/200000000000 : ℝ) (245162424629/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196129939703/200000000000 : ℝ) (245162424629/250000000000 : ℝ) (990324849257/1000000000000 : ℝ) (495162424629/500000000000 : ℝ) (247569396649/250000000000 : ℝ) (990277586597/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 1 (990324849257/1000000000000 : ℝ) (495162424629/500000000000 : ℝ) (247569396649/250000000000 : ℝ) (990277586597/1000000000000 : ℝ) (495150608963/500000000000 : ℝ) (123787652241/125000000000 : ℝ) (247575304411/250000000000 : ℝ) (495150608823/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 2 (495150608963/500000000000 : ℝ) (123787652241/125000000000 : ℝ) (247575304411/250000000000 : ℝ) (495150608823/500000000000 : ℝ) (198060243557/200000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 3 (198060243557/200000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 4 (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 5 (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 6 (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2241/16384 : ℝ)) 7 (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2241/16384 : ℝ))) (195770704653/1000000000000 : ℝ) (195770704659/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195770704653/1000000000000 : ℝ) (195770704659/1000000000000 : ℝ) (298942676163/500000000000 : ℝ) (59788535233/100000000000 : ℝ) (442459833943/1000000000000 : ℝ) (8849196679/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 1 (298942676163/500000000000 : ℝ) (59788535233/100000000000 : ℝ) (442459833943/1000000000000 : ℝ) (8849196679/20000000000 : ℝ) (260086296567/500000000000 : ℝ) (26008629657/50000000000 : ℝ) (514334768129/1000000000000 : ℝ) (64291846017/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 2 (260086296567/500000000000 : ℝ) (26008629657/50000000000 : ℝ) (514334768129/1000000000000 : ℝ) (64291846017/125000000000 : ℝ) (517253680631/1000000000000 : ℝ) (258626840319/500000000000 : ℝ) (517245444713/1000000000000 : ℝ) (6465568059/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 3 (517253680631/1000000000000 : ℝ) (258626840319/500000000000 : ℝ) (517245444713/1000000000000 : ℝ) (6465568059/12500000000 : ℝ) (32328097667/62500000000 : ℝ) (517249562679/1000000000000 : ℝ) (103449912531/200000000000 : ℝ) (517249562663/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 4 (32328097667/62500000000 : ℝ) (517249562679/1000000000000 : ℝ) (103449912531/200000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 5 (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 6 (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2241/16384 : ℝ))) 7 (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2241/16384 : ℝ)) hmem 8 (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2241/16384 : ℝ))) hcmem 8 (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2241/16384 : ℝ)) (123787652223/125000000000 : ℝ) (990301217787/1000000000000 : ℝ) (517249562663/1000000000000 : ℝ) (517249562671/1000000000000 : ℝ) (1640902179/2000000000 : ℝ) (205112772379/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0353_exp_lower
  have heNumeric : (80760440841/40000000000 : ℝ)/4 ≤ Real.exp (-10938985010381/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80760440841/40000000000 : ℝ)/4 ≤ Real.exp ((8963/65536 : ℝ)-(205112772379/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8963/65536 : ℝ) (2241/16384 : ℝ) (205112772379/250000000000 : ℝ) (80760440841/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0354; no trusted numerical premise.
theorem cover7_leaf0354_exp_radius : (997560212489539461/1000000000000000000 : ℝ) ≤ Real.exp ((-8965/458752 : ℝ)/8) ∧ Real.exp ((-8965/458752 : ℝ)/8) ≤ (498780106244769731/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8965/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0354_exp_lower : (57380569849321407/62500000000000000 : ℝ) ≤ Real.exp ((-2734746082867/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734746082867/4000000000000 : ℝ)/8) ≤ (918089117589142513/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734746082867/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0354_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802221339/200000000000 : ℝ) ≤ 4*Real.exp (2241/16384 : ℝ)*Real.exp (-mu (radius 7 (8965/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403802221339/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8965/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0354_exp_radius
  have hrNumeric : (980647560871/1000000000000 : ℝ) ≤ Real.exp (-8965/458752 : ℝ) ∧ Real.exp (-8965/458752 : ℝ) ≤ (122580945109/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980647560871/1000000000000 : ℝ) ≤ (radius 7 (8965/65536 : ℝ)) ∧ (radius 7 (8965/65536 : ℝ)) ≤ (122580945109/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8965/65536 : ℝ)) (980647560871/1000000000000 : ℝ) (122580945109/125000000000 : ℝ) (195781412181/1000000000000 : ℝ) (195781412187/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8965/65536 : ℝ)) (980647560871/1000000000000 : ℝ) (122580945109/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980647560871/1000000000000 : ℝ) (122580945109/125000000000 : ℝ) (198064756087/200000000000 : ℝ) (247580945109/250000000000 : ℝ) (12378456341/12500000000 : ℝ) (990276507281/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 1 (198064756087/200000000000 : ℝ) (247580945109/250000000000 : ℝ) (12378456341/12500000000 : ℝ) (990276507281/1000000000000 : ℝ) (990300143857/1000000000000 : ℝ) (990300143859/1000000000000 : ℝ) (39612005743/40000000000 : ℝ) (990300143577/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 2 (990300143857/1000000000000 : ℝ) (990300143859/1000000000000 : ℝ) (39612005743/40000000000 : ℝ) (990300143577/1000000000000 : ℝ) (247575035929/250000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 3 (247575035929/250000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 4 (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 5 (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 6 (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8965/65536 : ℝ)) 7 (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8965/65536 : ℝ))) (195781412181/1000000000000 : ℝ) (195781412187/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195781412181/1000000000000 : ℝ) (195781412187/1000000000000 : ℝ) (59789070609/100000000000 : ℝ) (298945353047/500000000000 : ℝ) (442471933777/1000000000000 : ℝ) (88494386757/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 1 (59789070609/100000000000 : ℝ) (298945353047/500000000000 : ℝ) (442471933777/1000000000000 : ℝ) (88494386757/200000000000 : ℝ) (520181319933/1000000000000 : ℝ) (26009065997/50000000000 : ℝ) (257172051801/500000000000 : ℝ) (51434410361/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 2 (520181319933/1000000000000 : ℝ) (26009065997/50000000000 : ℝ) (257172051801/500000000000 : ℝ) (51434410361/100000000000 : ℝ) (517262711767/1000000000000 : ℝ) (20690508471/40000000000 : ℝ) (51725447771/100000000000 : ℝ) (258627238859/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 3 (517262711767/1000000000000 : ℝ) (20690508471/40000000000 : ℝ) (51725447771/100000000000 : ℝ) (258627238859/500000000000 : ℝ) (258629297369/500000000000 : ℝ) (517258594747/1000000000000 : ℝ) (258629297361/500000000000 : ℝ) (517258594731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 4 (258629297369/500000000000 : ℝ) (517258594747/1000000000000 : ℝ) (258629297361/500000000000 : ℝ) (517258594731/1000000000000 : ℝ) (51725859473/100000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 5 (51725859473/100000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 6 (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8965/65536 : ℝ))) 7 (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8965/65536 : ℝ)) hmem 8 (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8965/65536 : ℝ))) hcmem 8 (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8965/65536 : ℝ)) (198060028743/200000000000 : ℝ) (495150071859/500000000000 : ℝ) (517258594729/1000000000000 : ℝ) (517258594739/1000000000000 : ℝ) (410233152927/500000000000 : ℝ) (820466305873/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0354_exp_lower
  have heNumeric : (403802221339/200000000000 : ℝ)/4 ≤ Real.exp (-2734746082867/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802221339/200000000000 : ℝ)/4 ≤ Real.exp ((2241/16384 : ℝ)-(820466305873/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2241/16384 : ℝ) (8965/65536 : ℝ) (820466305873/1000000000000 : ℝ) (403802221339/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0355; no trusted numerical premise.
theorem cover7_leaf0355_exp_radius : (249389985168997429/250000000000000000 : ℝ) ≤ Real.exp ((-4483/229376 : ℝ)/8) ∧ Real.exp ((-4483/229376 : ℝ)/8) ≤ (997559940675989717/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4483/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0355_exp_lower : (183617824517674893/200000000000000000 : ℝ) ≤ Real.exp ((-437559345379/640000000000 : ℝ)/8) ∧ Real.exp ((-437559345379/640000000000 : ℝ)/8) ≤ (459044561294187233/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437559345379/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0355_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376399331/125000000000 : ℝ) ≤ 4*Real.exp (8965/65536 : ℝ)*Real.exp (-mu (radius 7 (4483/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376399331/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4483/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0355_exp_radius
  have hrNumeric : (980645423231/1000000000000 : ℝ) ≤ Real.exp (-4483/229376 : ℝ) ∧ Real.exp (-4483/229376 : ℝ) ≤ (7661292369/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980645423231/1000000000000 : ℝ) ≤ (radius 7 (4483/32768 : ℝ)) ∧ (radius 7 (4483/32768 : ℝ)) ≤ (7661292369/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4483/32768 : ℝ)) (980645423231/1000000000000 : ℝ) (7661292369/7812500000 : ℝ) (4894802977/25000000000 : ℝ) (97896059543/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4483/32768 : ℝ)) (980645423231/1000000000000 : ℝ) (7661292369/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980645423231/1000000000000 : ℝ) (7661292369/7812500000 : ℝ) (198064542323/200000000000 : ℝ) (15473792369/15625000000 : ℝ) (247568856991/250000000000 : ℝ) (495137713983/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 1 (198064542323/200000000000 : ℝ) (15473792369/15625000000 : ℝ) (247568856991/250000000000 : ℝ) (495137713983/500000000000 : ℝ) (990299069789/1000000000000 : ℝ) (990299069791/1000000000000 : ℝ) (990299069507/1000000000000 : ℝ) (990299069509/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 2 (990299069789/1000000000000 : ℝ) (990299069791/1000000000000 : ℝ) (990299069507/1000000000000 : ℝ) (990299069509/1000000000000 : ℝ) (61893691853/62500000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 3 (61893691853/62500000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 4 (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 5 (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 6 (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4483/32768 : ℝ)) 7 (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4483/32768 : ℝ))) (4894802977/25000000000 : ℝ) (97896059543/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4894802977/25000000000 : ℝ) (97896059543/500000000000 : ℝ) (29894802977/50000000000 : ℝ) (597896059543/1000000000000 : ℝ) (44248403257/100000000000 : ℝ) (221242016289/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 1 (29894802977/50000000000 : ℝ) (597896059543/1000000000000 : ℝ) (44248403257/100000000000 : ℝ) (221242016289/500000000000 : ℝ) (104038009211/200000000000 : ℝ) (520190046061/1000000000000 : ℝ) (128588359573/250000000000 : ℝ) (514353438299/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 2 (104038009211/200000000000 : ℝ) (520190046061/1000000000000 : ℝ) (128588359573/250000000000 : ℝ) (514353438299/1000000000000 : ℝ) (517271742173/1000000000000 : ℝ) (25863587109/50000000000 : ℝ) (64657938747/125000000000 : ℝ) (16164484687/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 3 (517271742173/1000000000000 : ℝ) (25863587109/50000000000 : ℝ) (64657938747/125000000000 : ℝ) (16164484687/31250000000 : ℝ) (258633813037/500000000000 : ℝ) (258633813041/500000000000 : ℝ) (258633813029/500000000000 : ℝ) (258633813033/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 4 (258633813037/500000000000 : ℝ) (258633813041/500000000000 : ℝ) (258633813029/500000000000 : ℝ) (258633813033/500000000000 : ℝ) (258633813033/500000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 5 (258633813033/500000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 6 (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4483/32768 : ℝ))) 7 (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4483/32768 : ℝ)) hmem 8 (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4483/32768 : ℝ))) hcmem 8 (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4483/32768 : ℝ)) (990299069647/1000000000000 : ℝ) (19805981393/20000000000 : ℝ) (103453525213/200000000000 : ℝ) (258633813037/500000000000 : ℝ) (410240760541/500000000000 : ℝ) (8204815211/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0355_exp_lower
  have heNumeric : (252376399331/125000000000 : ℝ)/4 ≤ Real.exp (-437559345379/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376399331/125000000000 : ℝ)/4 ≤ Real.exp ((8965/65536 : ℝ)-(8204815211/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8965/65536 : ℝ) (4483/32768 : ℝ) (8204815211/10000000000 : ℝ) (252376399331/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0356; no trusted numerical premise.
theorem cover7_leaf0356_exp_radius : (498779834431257017/500000000000000000 : ℝ) ≤ Real.exp ((-1281/65536 : ℝ)/8) ∧ Real.exp ((-1281/65536 : ℝ)/8) ≤ (199511933772502807/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1281/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0356_exp_lower : (918089127717860341/1000000000000000000 : ℝ) ≤ Real.exp ((-5469491459661/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469491459661/8000000000000 : ℝ)/8) ≤ (459044563858930171/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469491459661/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0356_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011284891/1000000000000 : ℝ) ≤ 4*Real.exp (4483/32768 : ℝ)*Real.exp (-mu (radius 7 (8967/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011284891/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8967/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0356_exp_radius
  have hrNumeric : (245160821399/250000000000 : ℝ) ≤ Real.exp (-1281/65536 : ℝ) ∧ Real.exp (-1281/65536 : ℝ) ≤ (980643285597/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245160821399/250000000000 : ℝ) ≤ (radius 7 (8967/65536 : ℝ)) ∧ (radius 7 (8967/65536 : ℝ)) ≤ (980643285597/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8967/65536 : ℝ)) (245160821399/250000000000 : ℝ) (980643285597/1000000000000 : ℝ) (97901412673/500000000000 : ℝ) (24475353169/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8967/65536 : ℝ)) (245160821399/250000000000 : ℝ) (980643285597/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245160821399/250000000000 : ℝ) (980643285597/1000000000000 : ℝ) (495160821399/500000000000 : ℝ) (990321642799/1000000000000 : ℝ) (19805486973/20000000000 : ℝ) (247568587163/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 1 (495160821399/500000000000 : ℝ) (990321642799/1000000000000 : ℝ) (19805486973/20000000000 : ℝ) (247568587163/250000000000 : ℝ) (247574498931/250000000000 : ℝ) (495148997863/500000000000 : ℝ) (990297995441/1000000000000 : ℝ) (247574498861/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 2 (247574498931/250000000000 : ℝ) (495148997863/500000000000 : ℝ) (990297995441/1000000000000 : ℝ) (247574498861/250000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 3 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 4 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 5 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 6 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8967/65536 : ℝ)) 7 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8967/65536 : ℝ))) (97901412673/500000000000 : ℝ) (24475353169/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97901412673/500000000000 : ℝ) (24475353169/125000000000 : ℝ) (597901412673/1000000000000 : ℝ) (149475353169/250000000000 : ℝ) (442496130317/1000000000000 : ℝ) (17699845213/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 1 (597901412673/1000000000000 : ℝ) (149475353169/250000000000 : ℝ) (442496130317/1000000000000 : ℝ) (17699845213/40000000000 : ℝ) (104039754299/200000000000 : ℝ) (520198771501/1000000000000 : ℝ) (514362772193/1000000000000 : ℝ) (2571813861/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 2 (104039754299/200000000000 : ℝ) (520198771501/1000000000000 : ℝ) (514362772193/1000000000000 : ℝ) (2571813861/5000000000 : ℝ) (129320192961/250000000000 : ℝ) (517280771851/1000000000000 : ℝ) (517272541507/1000000000000 : ℝ) (258636270757/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 3 (129320192961/250000000000 : ℝ) (517280771851/1000000000000 : ℝ) (517272541507/1000000000000 : ℝ) (258636270757/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (517276656683/1000000000000 : ℝ) (517276656659/1000000000000 : ℝ) (517276656667/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 4 (20691066267/40000000000 : ℝ) (517276656683/1000000000000 : ℝ) (517276656659/1000000000000 : ℝ) (517276656667/1000000000000 : ℝ) (517276656667/1000000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 5 (517276656667/1000000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 6 (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8967/65536 : ℝ))) 7 (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8967/65536 : ℝ)) hmem 8 (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8967/65536 : ℝ))) hcmem 8 (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8967/65536 : ℝ)) (495148997791/500000000000 : ℝ) (198059599117/200000000000 : ℝ) (258638328333/500000000000 : ℝ) (20691066267/40000000000 : ℝ) (410248367587/500000000000 : ℝ) (102562091899/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0356_exp_lower
  have heNumeric : (2019011284891/1000000000000 : ℝ)/4 ≤ Real.exp (-5469491459661/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011284891/1000000000000 : ℝ)/4 ≤ Real.exp ((4483/32768 : ℝ)-(102562091899/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4483/32768 : ℝ) (8967/65536 : ℝ) (102562091899/125000000000 : ℝ) (2019011284891/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0357; no trusted numerical premise.
theorem cover7_leaf0357_exp_radius : (199511879409822483/200000000000000000 : ℝ) ≤ Real.exp ((-1121/57344 : ℝ)/8) ∧ Real.exp ((-1121/57344 : ℝ)/8) ≤ (31173731157784763/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1121/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0357_exp_lower : (229522283244170513/250000000000000000 : ℝ) ≤ Real.exp ((-10938982186137/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938982186137/16000000000000 : ℝ)/8) ≤ (918089132976682053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938982186137/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0357_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011377411/1000000000000 : ℝ) ≤ 4*Real.exp (8967/65536 : ℝ)*Real.exp (-mu (radius 7 (1121/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011377411/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1121/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0357_exp_radius
  have hrNumeric : (196128229593/200000000000 : ℝ) ≤ Real.exp (-1121/57344 : ℝ) ∧ Real.exp (-1121/57344 : ℝ) ≤ (490320573983/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196128229593/200000000000 : ℝ) ≤ (radius 7 (1121/8192 : ℝ)) ∧ (radius 7 (1121/8192 : ℝ)) ≤ (490320573983/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1121/8192 : ℝ)) (196128229593/200000000000 : ℝ) (490320573983/500000000000 : ℝ) (97906765491/500000000000 : ℝ) (48953382747/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1121/8192 : ℝ)) (196128229593/200000000000 : ℝ) (490320573983/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196128229593/200000000000 : ℝ) (490320573983/500000000000 : ℝ) (495160286991/500000000000 : ℝ) (990320573983/1000000000000 : ℝ) (990273269337/1000000000000 : ℝ) (990273269339/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 1 (495160286991/500000000000 : ℝ) (990320573983/1000000000000 : ℝ) (990273269337/1000000000000 : ℝ) (990273269339/1000000000000 : ℝ) (990296921659/1000000000000 : ℝ) (990296921661/1000000000000 : ℝ) (990296921377/1000000000000 : ℝ) (990296921379/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 2 (990296921659/1000000000000 : ℝ) (990296921661/1000000000000 : ℝ) (990296921377/1000000000000 : ℝ) (990296921379/1000000000000 : ℝ) (495148460759/500000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 3 (495148460759/500000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 4 (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 5 (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 6 (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1121/8192 : ℝ)) 7 (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1121/8192 : ℝ))) (97906765491/500000000000 : ℝ) (48953382747/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97906765491/500000000000 : ℝ) (48953382747/250000000000 : ℝ) (597906765491/1000000000000 : ℝ) (298953382747/500000000000 : ℝ) (442508227021/1000000000000 : ℝ) (442508227029/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 1 (597906765491/1000000000000 : ℝ) (298953382747/500000000000 : ℝ) (442508227021/1000000000000 : ℝ) (442508227029/1000000000000 : ℝ) (8128242129/15625000000 : ℝ) (260103748131/500000000000 : ℝ) (51437210531/100000000000 : ℝ) (514372105317/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 2 (8128242129/15625000000 : ℝ) (260103748131/500000000000 : ℝ) (51437210531/100000000000 : ℝ) (514372105317/1000000000000 : ℝ) (517289800783/1000000000000 : ℝ) (51728980079/100000000000 : ℝ) (103456314461/200000000000 : ℝ) (517281572313/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 3 (517289800783/1000000000000 : ℝ) (51728980079/100000000000 : ℝ) (103456314461/200000000000 : ℝ) (517281572313/1000000000000 : ℝ) (32330355409/62500000000 : ℝ) (64660710819/125000000000 : ℝ) (517285686527/1000000000000 : ℝ) (64660710817/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 4 (32330355409/62500000000 : ℝ) (64660710819/125000000000 : ℝ) (517285686527/1000000000000 : ℝ) (64660710817/125000000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 5 (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 6 (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1121/8192 : ℝ))) 7 (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1121/8192 : ℝ)) hmem 8 (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1121/8192 : ℝ))) hcmem 8 (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1121/8192 : ℝ)) (990296921517/1000000000000 : ℝ) (12378711519/12500000000 : ℝ) (103457137307/200000000000 : ℝ) (32330355409/62500000000 : ℝ) (820511948139/1000000000000 : ℝ) (820511948157/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0357_exp_lower
  have heNumeric : (2019011377411/1000000000000 : ℝ)/4 ≤ Real.exp (-10938982186137/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011377411/1000000000000 : ℝ)/4 ≤ Real.exp ((8967/65536 : ℝ)-(820511948157/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8967/65536 : ℝ) (1121/8192 : ℝ) (820511948157/1000000000000 : ℝ) (2019011377411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0358; no trusted numerical premise.
theorem cover7_leaf0358_exp_radius : (997559125235784859/1000000000000000000 : ℝ) ≤ Real.exp ((-8969/458752 : ℝ)/8) ∧ Real.exp ((-8969/458752 : ℝ)/8) ≤ (49877956261789243/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8969/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0358_exp_lower : (459044569183452651/500000000000000000 : ℝ) ≤ Real.exp ((-1367372679329/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367372679329/2000000000000 : ℝ)/8) ≤ (918089138366905303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367372679329/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0358_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505736121/500000000000 : ℝ) ≤ 4*Real.exp (1121/8192 : ℝ)*Real.exp (-mu (radius 7 (8969/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505736121/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8969/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0358_exp_radius
  have hrNumeric : (49031950517/50000000000 : ℝ) ≤ Real.exp (-8969/458752 : ℝ) ∧ Real.exp (-8969/458752 : ℝ) ≤ (980639010341/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49031950517/50000000000 : ℝ) ≤ (radius 7 (8969/65536 : ℝ)) ∧ (radius 7 (8969/65536 : ℝ)) ≤ (980639010341/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8969/65536 : ℝ)) (49031950517/50000000000 : ℝ) (980639010341/1000000000000 : ℝ) (9791211799/50000000000 : ℝ) (97912117993/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8969/65536 : ℝ)) (49031950517/50000000000 : ℝ) (980639010341/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49031950517/50000000000 : ℝ) (980639010341/1000000000000 : ℝ) (99031950517/100000000000 : ℝ) (990319505171/1000000000000 : ℝ) (495136095013/500000000000 : ℝ) (247568047507/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 1 (99031950517/100000000000 : ℝ) (990319505171/1000000000000 : ℝ) (495136095013/500000000000 : ℝ) (247568047507/250000000000 : ℝ) (495147923799/500000000000 : ℝ) (2475739619/2500000000 : ℝ) (198059169463/200000000000 : ℝ) (990295847317/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 2 (495147923799/500000000000 : ℝ) (2475739619/2500000000 : ℝ) (198059169463/200000000000 : ℝ) (990295847317/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 3 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 4 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 5 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 6 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8969/65536 : ℝ)) 7 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8969/65536 : ℝ))) (9791211799/50000000000 : ℝ) (97912117993/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9791211799/50000000000 : ℝ) (97912117993/500000000000 : ℝ) (59791211799/100000000000 : ℝ) (597912117993/1000000000000 : ℝ) (221260161337/500000000000 : ℝ) (221260161341/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 1 (59791211799/100000000000 : ℝ) (597912117993/1000000000000 : ℝ) (221260161337/500000000000 : ℝ) (221260161341/500000000000 : ℝ) (130054055083/250000000000 : ℝ) (260108110169/500000000000 : ℝ) (102876287527/200000000000 : ℝ) (257190718821/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 2 (130054055083/250000000000 : ℝ) (260108110169/500000000000 : ℝ) (102876287527/200000000000 : ℝ) (257190718821/500000000000 : ℝ) (517298828983/1000000000000 : ℝ) (51729882899/100000000000 : ℝ) (103458120473/200000000000 : ℝ) (129322650593/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 3 (517298828983/1000000000000 : ℝ) (51729882899/100000000000 : ℝ) (103458120473/200000000000 : ℝ) (129322650593/250000000000 : ℝ) (258647357837/500000000000 : ℝ) (517294715681/1000000000000 : ℝ) (517294715657/1000000000000 : ℝ) (103458943133/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 4 (258647357837/500000000000 : ℝ) (517294715681/1000000000000 : ℝ) (517294715657/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 5 (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 6 (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8969/65536 : ℝ))) 7 (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8969/65536 : ℝ)) hmem 8 (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8969/65536 : ℝ))) hcmem 8 (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8969/65536 : ℝ)) (30946745233/31250000000 : ℝ) (990295847459/1000000000000 : ℝ) (103458943133/200000000000 : ℝ) (517294715673/1000000000000 : ℝ) (820527159961/1000000000000 : ℝ) (820527159977/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0358_exp_lower
  have heNumeric : (1009505736121/500000000000 : ℝ)/4 ≤ Real.exp (-1367372679329/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505736121/500000000000 : ℝ)/4 ≤ Real.exp ((1121/8192 : ℝ)-(820527159977/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1121/8192 : ℝ) (8969/65536 : ℝ) (820527159977/1000000000000 : ℝ) (1009505736121/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0359; no trusted numerical premise.
theorem cover7_leaf0359_exp_radius : (997558853422531367/1000000000000000000 : ℝ) ≤ Real.exp ((-4485/229376 : ℝ)/8) ∧ Real.exp ((-4485/229376 : ℝ)/8) ≤ (124694856677816421/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4485/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0359_exp_lower : (229522285971558717/250000000000000000 : ℝ) ≤ Real.exp ((-10938980665127/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938980665127/16000000000000 : ℝ)/8) ≤ (918089143886234869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938980665127/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0359_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31547055771/15625000000 : ℝ) ≤ 4*Real.exp (8969/65536 : ℝ)*Real.exp (-mu (radius 7 (4485/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (31547055771/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4485/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0359_exp_radius
  have hrNumeric : (980636872719/1000000000000 : ℝ) ≤ Real.exp (-4485/229376 : ℝ) ∧ Real.exp (-4485/229376 : ℝ) ≤ (12257960909/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980636872719/1000000000000 : ℝ) ≤ (radius 7 (4485/32768 : ℝ)) ∧ (radius 7 (4485/32768 : ℝ)) ≤ (12257960909/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4485/32768 : ℝ)) (980636872719/1000000000000 : ℝ) (12257960909/12500000000 : ℝ) (3916698807/20000000000 : ℝ) (48958735089/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4485/32768 : ℝ)) (980636872719/1000000000000 : ℝ) (12257960909/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980636872719/1000000000000 : ℝ) (12257960909/12500000000 : ℝ) (990318436359/1000000000000 : ℝ) (24757960909/25000000000 : ℝ) (247567777679/250000000000 : ℝ) (990271110717/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 1 (990318436359/1000000000000 : ℝ) (24757960909/25000000000 : ℝ) (247567777679/250000000000 : ℝ) (990271110717/1000000000000 : ℝ) (990294773537/1000000000000 : ℝ) (990294773539/1000000000000 : ℝ) (495147386627/500000000000 : ℝ) (123786846657/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 2 (990294773537/1000000000000 : ℝ) (990294773539/1000000000000 : ℝ) (495147386627/500000000000 : ℝ) (123786846657/125000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 3 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 4 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 5 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 6 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4485/32768 : ℝ)) 7 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4485/32768 : ℝ))) (3916698807/20000000000 : ℝ) (48958735089/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3916698807/20000000000 : ℝ) (48958735089/250000000000 : ℝ) (23916698807/40000000000 : ℝ) (298958735089/500000000000 : ℝ) (442532417287/1000000000000 : ℝ) (221266208647/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 1 (23916698807/40000000000 : ℝ) (298958735089/500000000000 : ℝ) (442532417287/1000000000000 : ℝ) (221266208647/500000000000 : ℝ) (520224943731/1000000000000 : ℝ) (65028117967/125000000000 : ℝ) (514390769177/1000000000000 : ℝ) (514390769183/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 2 (520224943731/1000000000000 : ℝ) (65028117967/125000000000 : ℝ) (514390769177/1000000000000 : ℝ) (514390769183/1000000000000 : ℝ) (258653928227/500000000000 : ℝ) (25865392823/50000000000 : ℝ) (258649815847/500000000000 : ℝ) (5172996317/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 3 (258653928227/500000000000 : ℝ) (25865392823/50000000000 : ℝ) (258649815847/500000000000 : ℝ) (5172996317/10000000000 : ℝ) (258651872037/500000000000 : ℝ) (6466296801/12500000000 : ℝ) (517303744057/1000000000000 : ℝ) (8082871001/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 4 (258651872037/500000000000 : ℝ) (6466296801/12500000000 : ℝ) (517303744057/1000000000000 : ℝ) (8082871001/15625000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 5 (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 6 (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4485/32768 : ℝ))) 7 (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4485/32768 : ℝ)) hmem 8 (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4485/32768 : ℝ))) hcmem 8 (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4485/32768 : ℝ)) (198058954679/200000000000 : ℝ) (495147386699/500000000000 : ℝ) (103460748813/200000000000 : ℝ) (64662968009/125000000000 : ℝ) (410271185329/500000000000 : ℝ) (51283898167/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0359_exp_lower
  have heNumeric : (31547055771/15625000000 : ℝ)/4 ≤ Real.exp (-10938980665127/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31547055771/15625000000 : ℝ)/4 ≤ Real.exp ((8969/65536 : ℝ)-(51283898167/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8969/65536 : ℝ) (4485/32768 : ℝ) (51283898167/62500000000 : ℝ) (31547055771/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0360; no trusted numerical premise.
theorem cover7_leaf0360_exp_radius : (498779290804675969/500000000000000000 : ℝ) ≤ Real.exp ((-8971/458752 : ℝ)/8) ∧ Real.exp ((-8971/458752 : ℝ)/8) ≤ (997558581609351939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8971/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0360_exp_lower : (229522287383696379/250000000000000000 : ℝ) ≤ Real.exp ((-5469489938803/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469489938803/8000000000000 : ℝ)/8) ≤ (918089149534785517/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469489938803/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0360_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25237645859/12500000000 : ℝ) ≤ 4*Real.exp (4485/32768 : ℝ)*Real.exp (-mu (radius 7 (8971/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (25237645859/12500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8971/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0360_exp_radius
  have hrNumeric : (490317367551/500000000000 : ℝ) ≤ Real.exp (-8971/458752 : ℝ) ∧ Real.exp (-8971/458752 : ℝ) ≤ (980634735103/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490317367551/500000000000 : ℝ) ≤ (radius 7 (8971/65536 : ℝ)) ∧ (radius 7 (8971/65536 : ℝ)) ≤ (980634735103/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8971/65536 : ℝ)) (490317367551/500000000000 : ℝ) (980634735103/1000000000000 : ℝ) (195845644091/1000000000000 : ℝ) (195845644097/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8971/65536 : ℝ)) (490317367551/500000000000 : ℝ) (980634735103/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490317367551/500000000000 : ℝ) (980634735103/1000000000000 : ℝ) (990317367551/1000000000000 : ℝ) (3868427217/3906250000 : ℝ) (495135015703/500000000000 : ℝ) (61891876963/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 1 (990317367551/1000000000000 : ℝ) (3868427217/3906250000 : ℝ) (495135015703/500000000000 : ℝ) (61891876963/62500000000 : ℝ) (495146849739/500000000000 : ℝ) (24757342487/25000000000 : ℝ) (198058739839/200000000000 : ℝ) (495146849599/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 2 (495146849739/500000000000 : ℝ) (24757342487/25000000000 : ℝ) (198058739839/200000000000 : ℝ) (495146849599/500000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 3 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 4 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 5 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 6 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8971/65536 : ℝ)) 7 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8971/65536 : ℝ))) (195845644091/1000000000000 : ℝ) (195845644097/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195845644091/1000000000000 : ℝ) (195845644097/1000000000000 : ℝ) (119584564409/200000000000 : ℝ) (597922822049/1000000000000 : ℝ) (221272255429/500000000000 : ℝ) (221272255433/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 1 (119584564409/200000000000 : ℝ) (597922822049/1000000000000 : ℝ) (221272255429/500000000000 : ℝ) (221272255433/500000000000 : ℝ) (520233666451/1000000000000 : ℝ) (260116833229/500000000000 : ℝ) (257200049967/500000000000 : ℝ) (514400099941/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 2 (520233666451/1000000000000 : ℝ) (260116833229/500000000000 : ℝ) (257200049967/500000000000 : ℝ) (514400099941/1000000000000 : ℝ) (64664610399/125000000000 : ℝ) (80830763/156250000 : ℝ) (51730866029/100000000000 : ℝ) (258654330149/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 3 (64664610399/125000000000 : ℝ) (80830763/156250000 : ℝ) (51730866029/100000000000 : ℝ) (258654330149/500000000000 : ℝ) (517312771741/1000000000000 : ℝ) (517312771749/1000000000000 : ℝ) (129328192931/250000000000 : ℝ) (517312771733/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 4 (517312771741/1000000000000 : ℝ) (517312771749/1000000000000 : ℝ) (129328192931/250000000000 : ℝ) (517312771733/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 5 (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 6 (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8971/65536 : ℝ))) 7 (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8971/65536 : ℝ)) hmem 8 (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8971/65536 : ℝ))) hcmem 8 (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8971/65536 : ℝ)) (123786712417/125000000000 : ℝ) (990293699339/1000000000000 : ℝ) (129328192933/250000000000 : ℝ) (517312771741/1000000000000 : ℝ) (12821212191/15625000000 : ℝ) (820557580241/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0360_exp_lower
  have heNumeric : (25237645859/12500000000 : ℝ)/4 ≤ Real.exp (-5469489938803/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25237645859/12500000000 : ℝ)/4 ≤ Real.exp ((4485/32768 : ℝ)-(820557580241/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4485/32768 : ℝ) (8971/65536 : ℝ) (820557580241/1000000000000 : ℝ) (25237645859/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0361; no trusted numerical premise.
theorem cover7_leaf0361_exp_radius : (249389577449061643/250000000000000000 : ℝ) ≤ Real.exp ((-2243/114688 : ℝ)/8) ∧ Real.exp ((-2243/114688 : ℝ)/8) ≤ (997558309796246573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2243/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0361_exp_lower : (918089155313704859/1000000000000000000 : ℝ) ≤ Real.exp ((-10938979071909/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938979071909/16000000000000 : ℝ)/8) ≤ (45904457765685243/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938979071909/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0361_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901177039/100000000000 : ℝ) ≤ 4*Real.exp (8971/65536 : ℝ)*Real.exp (-mu (radius 7 (2243/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (201901177039/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2243/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0361_exp_radius
  have hrNumeric : (98063259749/100000000000 : ℝ) ≤ Real.exp (-2243/114688 : ℝ) ∧ Real.exp (-2243/114688 : ℝ) ≤ (980632597491/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98063259749/100000000000 : ℝ) ≤ (radius 7 (2243/16384 : ℝ)) ∧ (radius 7 (2243/16384 : ℝ)) ≤ (980632597491/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2243/16384 : ℝ)) (98063259749/100000000000 : ℝ) (980632597491/1000000000000 : ℝ) (97928173599/500000000000 : ℝ) (48964086801/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2243/16384 : ℝ)) (98063259749/100000000000 : ℝ) (980632597491/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98063259749/100000000000 : ℝ) (980632597491/1000000000000 : ℝ) (198063259749/200000000000 : ℝ) (495158149373/500000000000 : ℝ) (495134476049/500000000000 : ℝ) (990268952099/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 1 (198063259749/200000000000 : ℝ) (495158149373/500000000000 : ℝ) (495134476049/500000000000 : ℝ) (990268952099/1000000000000 : ℝ) (990292625421/1000000000000 : ℝ) (990292625423/1000000000000 : ℝ) (495146312569/500000000000 : ℝ) (49514631257/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 2 (990292625421/1000000000000 : ℝ) (990292625423/1000000000000 : ℝ) (495146312569/500000000000 : ℝ) (49514631257/50000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 3 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 4 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 5 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 6 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2243/16384 : ℝ)) 7 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2243/16384 : ℝ))) (97928173599/500000000000 : ℝ) (48964086801/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97928173599/500000000000 : ℝ) (48964086801/250000000000 : ℝ) (597928173599/1000000000000 : ℝ) (298964086801/500000000000 : ℝ) (442556603383/1000000000000 : ℝ) (44255660339/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 1 (597928173599/1000000000000 : ℝ) (298964086801/500000000000 : ℝ) (442556603383/1000000000000 : ℝ) (44255660339/100000000000 : ℝ) (520242388491/1000000000000 : ℝ) (32515149281/62500000000 : ℝ) (32150589369/62500000000 : ℝ) (514409429911/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 2 (520242388491/1000000000000 : ℝ) (32515149281/62500000000 : ℝ) (32150589369/62500000000 : ℝ) (514409429911/1000000000000 : ℝ) (517325909197/1000000000000 : ℝ) (129331477301/250000000000 : ℝ) (64664711019/125000000000 : ℝ) (517317688159/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 3 (517325909197/1000000000000 : ℝ) (129331477301/250000000000 : ℝ) (64664711019/125000000000 : ℝ) (517317688159/1000000000000 : ℝ) (258660899337/500000000000 : ℝ) (258660899341/500000000000 : ℝ) (258660899329/500000000000 : ℝ) (258660899333/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 4 (258660899337/500000000000 : ℝ) (258660899341/500000000000 : ℝ) (258660899329/500000000000 : ℝ) (258660899333/500000000000 : ℝ) (258660899333/500000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 5 (258660899333/500000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 6 (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2243/16384 : ℝ))) 7 (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2243/16384 : ℝ)) hmem 8 (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2243/16384 : ℝ))) hcmem 8 (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2243/16384 : ℝ)) (990292625279/1000000000000 : ℝ) (495146312641/500000000000 : ℝ) (103464359733/200000000000 : ℝ) (258660899337/500000000000 : ℝ) (51285799291/62500000000 : ℝ) (410286394337/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0361_exp_lower
  have heNumeric : (201901177039/100000000000 : ℝ)/4 ≤ Real.exp (-10938979071909/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901177039/100000000000 : ℝ)/4 ≤ Real.exp ((8971/65536 : ℝ)-(410286394337/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8971/65536 : ℝ) (2243/16384 : ℝ) (410286394337/500000000000 : ℝ) (201901177039/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0362; no trusted numerical premise.
theorem cover7_leaf0362_exp_radius : (997558037983215269/1000000000000000000 : ℝ) ≤ Real.exp ((-8973/458752 : ℝ)/8) ∧ Real.exp ((-8973/458752 : ℝ)/8) ≤ (99755803798321527/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8973/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0362_exp_lower : (918089161222419093/1000000000000000000 : ℝ) ≤ Real.exp ((-2734744562029/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734744562029/4000000000000 : ℝ)/8) ≤ (459044580611209547/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734744562029/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0362_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011874343/1000000000000 : ℝ) ≤ 4*Real.exp (2243/16384 : ℝ)*Real.exp (-mu (radius 7 (8973/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011874343/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8973/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0362_exp_radius
  have hrNumeric : (980630459883/1000000000000 : ℝ) ≤ Real.exp (-8973/458752 : ℝ) ∧ Real.exp (-8973/458752 : ℝ) ≤ (245157614971/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980630459883/1000000000000 : ℝ) ≤ (radius 7 (8973/65536 : ℝ)) ∧ (radius 7 (8973/65536 : ℝ)) ≤ (245157614971/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8973/65536 : ℝ)) (980630459883/1000000000000 : ℝ) (245157614971/250000000000 : ℝ) (195867049673/1000000000000 : ℝ) (195867049679/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8973/65536 : ℝ)) (980630459883/1000000000000 : ℝ) (245157614971/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980630459883/1000000000000 : ℝ) (245157614971/250000000000 : ℝ) (990315229941/1000000000000 : ℝ) (495157614971/500000000000 : ℝ) (990267872791/1000000000000 : ℝ) (990267872793/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 1 (990315229941/1000000000000 : ℝ) (495157614971/500000000000 : ℝ) (990267872791/1000000000000 : ℝ) (990267872793/1000000000000 : ℝ) (495145775683/500000000000 : ℝ) (123786443921/125000000000 : ℝ) (495145775541/500000000000 : ℝ) (198058310217/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 2 (495145775683/500000000000 : ℝ) (123786443921/125000000000 : ℝ) (495145775541/500000000000 : ℝ) (198058310217/200000000000 : ℝ) (123786443903/125000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 3 (123786443903/125000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 4 (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 5 (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 6 (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8973/65536 : ℝ)) 7 (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8973/65536 : ℝ))) (195867049673/1000000000000 : ℝ) (195867049679/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195867049673/1000000000000 : ℝ) (195867049679/1000000000000 : ℝ) (149483381209/250000000000 : ℝ) (14948338121/25000000000 : ℝ) (442568694863/1000000000000 : ℝ) (442568694871/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 1 (149483381209/250000000000 : ℝ) (14948338121/25000000000 : ℝ) (442568694863/1000000000000 : ℝ) (442568694871/1000000000000 : ℝ) (520251109849/1000000000000 : ℝ) (16257847183/31250000000 : ℝ) (514418759087/1000000000000 : ℝ) (102883751819/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 2 (520251109849/1000000000000 : ℝ) (16257847183/31250000000 : ℝ) (514418759087/1000000000000 : ℝ) (102883751819/200000000000 : ℝ) (129333733617/250000000000 : ℝ) (129333733619/250000000000 : ℝ) (517326715279/1000000000000 : ℝ) (64665839411/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 3 (129333733617/250000000000 : ℝ) (129333733619/250000000000 : ℝ) (517326715279/1000000000000 : ℝ) (64665839411/125000000000 : ℝ) (517330824873/1000000000000 : ℝ) (258665412441/500000000000 : ℝ) (517330824857/1000000000000 : ℝ) (258665412433/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 4 (517330824873/1000000000000 : ℝ) (258665412441/500000000000 : ℝ) (517330824857/1000000000000 : ℝ) (258665412433/500000000000 : ℝ) (103466164973/200000000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 5 (103466164973/200000000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 6 (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8973/65536 : ℝ))) 7 (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8973/65536 : ℝ)) hmem 8 (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8973/65536 : ℝ))) hcmem 8 (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8973/65536 : ℝ)) (990291551223/1000000000000 : ℝ) (990291551227/1000000000000 : ℝ) (16166588277/31250000000 : ℝ) (258665412437/500000000000 : ℝ) (205146998989/250000000000 : ℝ) (102573499497/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0362_exp_lower
  have heNumeric : (2019011874343/1000000000000 : ℝ)/4 ≤ Real.exp (-2734744562029/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011874343/1000000000000 : ℝ)/4 ≤ Real.exp ((2243/16384 : ℝ)-(102573499497/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2243/16384 : ℝ) (8973/65536 : ℝ) (102573499497/125000000000 : ℝ) (2019011874343/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0363; no trusted numerical premise.
theorem cover7_leaf0363_exp_radius : (997557766170258029/1000000000000000000 : ℝ) ≤ Real.exp ((-641/32768 : ℝ)/8) ∧ Real.exp ((-641/32768 : ℝ)/8) ≤ (99755776617025803/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-641/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0363_exp_lower : (918089167261731549/1000000000000000000 : ℝ) ≤ Real.exp ((-2187795481223/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187795481223/3200000000000 : ℝ)/8) ≤ (18361783345234631/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187795481223/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0363_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011980593/1000000000000 : ℝ) ≤ 4*Real.exp (8973/65536 : ℝ)*Real.exp (-mu (radius 7 (4487/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011980593/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4487/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0363_exp_radius
  have hrNumeric : (980628322281/1000000000000 : ℝ) ≤ Real.exp (-641/32768 : ℝ) ∧ Real.exp (-641/32768 : ℝ) ≤ (490314161141/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980628322281/1000000000000 : ℝ) ≤ (radius 7 (4487/32768 : ℝ)) ∧ (radius 7 (4487/32768 : ℝ)) ≤ (490314161141/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4487/32768 : ℝ)) (980628322281/1000000000000 : ℝ) (490314161141/500000000000 : ℝ) (97938875757/500000000000 : ℝ) (1224235947/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4487/32768 : ℝ)) (980628322281/1000000000000 : ℝ) (490314161141/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980628322281/1000000000000 : ℝ) (490314161141/500000000000 : ℝ) (49515708057/50000000000 : ℝ) (990314161141/1000000000000 : ℝ) (198053358697/200000000000 : ℝ) (990266793487/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 1 (49515708057/50000000000 : ℝ) (990314161141/1000000000000 : ℝ) (198053358697/200000000000 : ℝ) (990266793487/1000000000000 : ℝ) (3868322177/3906250000 : ℝ) (495145238657/500000000000 : ℝ) (990290477029/1000000000000 : ℝ) (990290477031/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 2 (3868322177/3906250000 : ℝ) (495145238657/500000000000 : ℝ) (990290477029/1000000000000 : ℝ) (990290477031/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 3 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 4 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 5 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 6 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4487/32768 : ℝ)) 7 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4487/32768 : ℝ))) (97938875757/500000000000 : ℝ) (1224235947/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97938875757/500000000000 : ℝ) (1224235947/6250000000 : ℝ) (597938875757/1000000000000 : ℝ) (7474235947/12500000000 : ℝ) (27661299081/62500000000 : ℝ) (55322598163/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 1 (597938875757/1000000000000 : ℝ) (7474235947/12500000000 : ℝ) (27661299081/62500000000 : ℝ) (55322598163/125000000000 : ℝ) (260129915263/500000000000 : ℝ) (130064957633/250000000000 : ℝ) (514428087483/1000000000000 : ℝ) (51442808749/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 2 (260129915263/500000000000 : ℝ) (130064957633/250000000000 : ℝ) (514428087483/1000000000000 : ℝ) (51442808749/100000000000 : ℝ) (129335989751/250000000000 : ℝ) (517343959011/1000000000000 : ℝ) (64666967709/125000000000 : ℝ) (517335741679/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 3 (129335989751/250000000000 : ℝ) (517343959011/1000000000000 : ℝ) (64666967709/125000000000 : ℝ) (517335741679/1000000000000 : ℝ) (258669925169/500000000000 : ℝ) (103467970069/200000000000 : ℝ) (517339850321/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 4 (258669925169/500000000000 : ℝ) (103467970069/200000000000 : ℝ) (517339850321/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 5 (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 6 (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4487/32768 : ℝ))) 7 (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4487/32768 : ℝ)) hmem 8 (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4487/32768 : ℝ))) hcmem 8 (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4487/32768 : ℝ)) (99029047717/100000000000 : ℝ) (990290477173/1000000000000 : ℝ) (517339850329/1000000000000 : ℝ) (517339850337/1000000000000 : ℝ) (205150800531/250000000000 : ℝ) (41030160107/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0363_exp_lower
  have heNumeric : (2019011980593/1000000000000 : ℝ)/4 ≤ Real.exp (-2187795481223/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011980593/1000000000000 : ℝ)/4 ≤ Real.exp ((8973/65536 : ℝ)-(41030160107/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8973/65536 : ℝ) (4487/32768 : ℝ) (41030160107/50000000000 : ℝ) (2019011980593/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0364; no trusted numerical premise.
theorem cover7_leaf0364_exp_radius : (997557494357374853/1000000000000000000 : ℝ) ≤ Real.exp ((-8975/458752 : ℝ)/8) ∧ Real.exp ((-8975/458752 : ℝ)/8) ≤ (498778747178687427/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8975/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0364_exp_lower : (229522293357480203/250000000000000000 : ℝ) ≤ Real.exp ((-5469488273073/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469488273073/8000000000000 : ℝ)/8) ≤ (918089173429920813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469488273073/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0364_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012089111/1000000000000 : ℝ) ≤ 4*Real.exp (4487/32768 : ℝ)*Real.exp (-mu (radius 7 (8975/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012089111/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8975/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0364_exp_radius
  have hrNumeric : (980626184683/1000000000000 : ℝ) ≤ Real.exp (-8975/458752 : ℝ) ∧ Real.exp (-8975/458752 : ℝ) ≤ (245156546171/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980626184683/1000000000000 : ℝ) ≤ (radius 7 (8975/65536 : ℝ)) ∧ (radius 7 (8975/65536 : ℝ)) ≤ (245156546171/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8975/65536 : ℝ)) (980626184683/1000000000000 : ℝ) (245156546171/250000000000 : ℝ) (195888452727/1000000000000 : ℝ) (195888452733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8975/65536 : ℝ)) (980626184683/1000000000000 : ℝ) (245156546171/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980626184683/1000000000000 : ℝ) (245156546171/250000000000 : ℝ) (990313092341/1000000000000 : ℝ) (495156546171/500000000000 : ℝ) (990265714181/1000000000000 : ℝ) (495132857091/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 1 (990313092341/1000000000000 : ℝ) (495156546171/500000000000 : ℝ) (990265714181/1000000000000 : ℝ) (495132857091/500000000000 : ℝ) (990289403261/1000000000000 : ℝ) (495144701631/500000000000 : ℝ) (990289402977/1000000000000 : ℝ) (990289402979/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 2 (990289403261/1000000000000 : ℝ) (495144701631/500000000000 : ℝ) (990289402977/1000000000000 : ℝ) (990289402979/1000000000000 : ℝ) (990289403119/1000000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 3 (990289403119/1000000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 4 (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 5 (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 6 (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8975/65536 : ℝ)) 7 (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8975/65536 : ℝ))) (195888452727/1000000000000 : ℝ) (195888452733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195888452727/1000000000000 : ℝ) (195888452733/1000000000000 : ℝ) (597944226363/1000000000000 : ℝ) (597944226367/1000000000000 : ℝ) (44259287469/100000000000 : ℝ) (221296437349/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 1 (597944226363/1000000000000 : ℝ) (597944226367/1000000000000 : ℝ) (44259287469/100000000000 : ℝ) (221296437349/500000000000 : ℝ) (260134275263/500000000000 : ℝ) (520268550533/1000000000000 : ℝ) (102887483019/200000000000 : ℝ) (514437415103/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 2 (260134275263/500000000000 : ℝ) (520268550533/1000000000000 : ℝ) (102887483019/200000000000 : ℝ) (514437415103/1000000000000 : ℝ) (51735298281/100000000000 : ℝ) (258676491409/500000000000 : ℝ) (517344767333/1000000000000 : ℝ) (258672383671/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 3 (51735298281/100000000000 : ℝ) (258676491409/500000000000 : ℝ) (517344767333/1000000000000 : ℝ) (258672383671/500000000000 : ℝ) (517348875071/1000000000000 : ℝ) (12933721877/25000000000 : ℝ) (103469775011/200000000000 : ℝ) (64668609383/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 4 (517348875071/1000000000000 : ℝ) (12933721877/25000000000 : ℝ) (103469775011/200000000000 : ℝ) (64668609383/125000000000 : ℝ) (517348875063/1000000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 5 (517348875063/1000000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 6 (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8975/65536 : ℝ))) 7 (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8975/65536 : ℝ)) hmem 8 (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8975/65536 : ℝ))) hcmem 8 (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8975/65536 : ℝ)) (495144701559/500000000000 : ℝ) (990289403121/1000000000000 : ℝ) (258674437531/500000000000 : ℝ) (8083576173/15625000000 : ℝ) (410309203581/500000000000 : ℝ) (820618407181/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0364_exp_lower
  have heNumeric : (2019012089111/1000000000000 : ℝ)/4 ≤ Real.exp (-5469488273073/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012089111/1000000000000 : ℝ)/4 ≤ Real.exp ((4487/32768 : ℝ)-(820618407181/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4487/32768 : ℝ) (8975/65536 : ℝ) (820618407181/1000000000000 : ℝ) (2019012089111/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0365; no trusted numerical premise.
theorem cover7_leaf0365_exp_radius : (997557222544565739/1000000000000000000 : ℝ) ≤ Real.exp ((-561/28672 : ℝ)/8) ∧ Real.exp ((-561/28672 : ℝ)/8) ≤ (49877861127228287/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-561/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0365_exp_lower : (918089179728134497/1000000000000000000 : ℝ) ≤ Real.exp ((-10938975668049/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938975668049/16000000000000 : ℝ)/8) ≤ (459044589864067249/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938975668049/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0365_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012199917/1000000000000 : ℝ) ≤ 4*Real.exp (8975/65536 : ℝ)*Real.exp (-mu (radius 7 (561/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012199917/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (561/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0365_exp_radius
  have hrNumeric : (98062404709/100000000000 : ℝ) ≤ Real.exp (-561/28672 : ℝ) ∧ Real.exp (-561/28672 : ℝ) ≤ (980624047091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98062404709/100000000000 : ℝ) ≤ (radius 7 (561/4096 : ℝ)) ∧ (radius 7 (561/4096 : ℝ)) ≤ (980624047091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (561/4096 : ℝ)) (98062404709/100000000000 : ℝ) (980624047091/1000000000000 : ℝ) (48974788327/250000000000 : ℝ) (97949576657/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (561/4096 : ℝ)) (98062404709/100000000000 : ℝ) (980624047091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (561/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98062404709/100000000000 : ℝ) (980624047091/1000000000000 : ℝ) (198062404709/200000000000 : ℝ) (495156011773/500000000000 : ℝ) (990264634877/1000000000000 : ℝ) (990264634879/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (561/4096 : ℝ)) 1 (198062404709/200000000000 : ℝ) (495156011773/500000000000 : ℝ) (990264634877/1000000000000 : ℝ) (990264634879/1000000000000 : ℝ) (990288329211/1000000000000 : ℝ) (990288329213/1000000000000 : ℝ) (990288328927/1000000000000 : ℝ) (99028832893/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (561/4096 : ℝ)) 2 (990288329211/1000000000000 : ℝ) (990288329213/1000000000000 : ℝ) (990288328927/1000000000000 : ℝ) (99028832893/100000000000 : ℝ) (990288329069/1000000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (561/4096 : ℝ)) 3 (990288329069/1000000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (561/4096 : ℝ)) 4 (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (561/4096 : ℝ)) 5 (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (561/4096 : ℝ)) 6 (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (561/4096 : ℝ)) 7 (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (561/4096 : ℝ))) (48974788327/250000000000 : ℝ) (97949576657/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48974788327/250000000000 : ℝ) (97949576657/500000000000 : ℝ) (298974788327/500000000000 : ℝ) (597949576657/1000000000000 : ℝ) (2766281019/6250000000 : ℝ) (55325620381/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 1 (298974788327/500000000000 : ℝ) (597949576657/1000000000000 : ℝ) (2766281019/6250000000 : ℝ) (55325620381/125000000000 : ℝ) (520277269847/1000000000000 : ℝ) (520277269853/1000000000000 : ℝ) (257223370961/500000000000 : ℝ) (514446741929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 2 (520277269847/1000000000000 : ℝ) (520277269853/1000000000000 : ℝ) (257223370961/500000000000 : ℝ) (514446741929/1000000000000 : ℝ) (129340501471/250000000000 : ℝ) (517362005891/1000000000000 : ℝ) (258676896131/500000000000 : ℝ) (51735379227/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 3 (129340501471/250000000000 : ℝ) (517362005891/1000000000000 : ℝ) (258676896131/500000000000 : ℝ) (51735379227/100000000000 : ℝ) (517357899073/1000000000000 : ℝ) (517357899081/1000000000000 : ℝ) (32334868691/62500000000 : ℝ) (103471579813/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 4 (517357899073/1000000000000 : ℝ) (517357899081/1000000000000 : ℝ) (32334868691/62500000000 : ℝ) (103471579813/200000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 5 (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 6 (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (561/4096 : ℝ))) 7 (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (561/4096 : ℝ)) hmem 8 (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (561/4096 : ℝ))) hcmem 8 (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (561/4096 : ℝ)) (247572082267/250000000000 : ℝ) (61893020567/62500000000 : ℝ) (64669737383/125000000000 : ℝ) (517357899073/1000000000000 : ℝ) (820633611071/1000000000000 : ℝ) (820633611089/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0365_exp_lower
  have heNumeric : (2019012199917/1000000000000 : ℝ)/4 ≤ Real.exp (-10938975668049/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012199917/1000000000000 : ℝ)/4 ≤ Real.exp ((8975/65536 : ℝ)-(820633611089/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8975/65536 : ℝ) (561/4096 : ℝ) (820633611089/1000000000000 : ℝ) (2019012199917/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0366; no trusted numerical premise.
theorem cover7_leaf0366_exp_radius : (997556950731830689/1000000000000000000 : ℝ) ≤ Real.exp ((-8977/458752 : ℝ)/8) ∧ Real.exp ((-8977/458752 : ℝ)/8) ≤ (99755695073183069/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8977/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0366_exp_lower : (114761148269560921/125000000000000000 : ℝ) ≤ Real.exp ((-341842961619/500000000000 : ℝ)/8) ∧ Real.exp ((-341842961619/500000000000 : ℝ)/8) ≤ (918089186156487369/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341842961619/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0366_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753078253/250000000000 : ℝ) ≤ 4*Real.exp (561/4096 : ℝ)*Real.exp (-mu (radius 7 (8977/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504753078253/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8977/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0366_exp_radius
  have hrNumeric : (490310954751/500000000000 : ℝ) ≤ Real.exp (-8977/458752 : ℝ) ∧ Real.exp (-8977/458752 : ℝ) ≤ (980621909503/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490310954751/500000000000 : ℝ) ≤ (radius 7 (8977/65536 : ℝ)) ∧ (radius 7 (8977/65536 : ℝ)) ≤ (980621909503/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8977/65536 : ℝ)) (490310954751/500000000000 : ℝ) (980621909503/1000000000000 : ℝ) (39181970651/200000000000 : ℝ) (195909853261/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8977/65536 : ℝ)) (490310954751/500000000000 : ℝ) (980621909503/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490310954751/500000000000 : ℝ) (980621909503/1000000000000 : ℝ) (990310954751/1000000000000 : ℝ) (3868402167/3906250000 : ℝ) (39610542223/40000000000 : ℝ) (990263555577/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 1 (990310954751/1000000000000 : ℝ) (3868402167/3906250000 : ℝ) (39610542223/40000000000 : ℝ) (990263555577/1000000000000 : ℝ) (990287255163/1000000000000 : ℝ) (198057451033/200000000000 : ℝ) (990287254879/1000000000000 : ℝ) (990287254881/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 2 (990287255163/1000000000000 : ℝ) (198057451033/200000000000 : ℝ) (990287254879/1000000000000 : ℝ) (990287254881/1000000000000 : ℝ) (990287255021/1000000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 3 (990287255021/1000000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 4 (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 5 (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 6 (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8977/65536 : ℝ)) 7 (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8977/65536 : ℝ))) (39181970651/200000000000 : ℝ) (195909853261/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39181970651/200000000000 : ℝ) (195909853261/1000000000000 : ℝ) (597954926627/1000000000000 : ℝ) (597954926631/1000000000000 : ℝ) (442617050343/1000000000000 : ℝ) (442617050351/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 1 (597954926627/1000000000000 : ℝ) (597954926631/1000000000000 : ℝ) (442617050343/1000000000000 : ℝ) (442617050351/1000000000000 : ℝ) (104057197697/200000000000 : ℝ) (520285988491/1000000000000 : ℝ) (12861401699/25000000000 : ℝ) (4019188031/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 2 (104057197697/200000000000 : ℝ) (520285988491/1000000000000 : ℝ) (12861401699/25000000000 : ℝ) (4019188031/7812500000 : ℝ) (258685514111/500000000000 : ℝ) (51737102823/100000000000 : ℝ) (103472563291/200000000000 : ℝ) (517362816463/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 3 (258685514111/500000000000 : ℝ) (51737102823/100000000000 : ℝ) (103472563291/200000000000 : ℝ) (517362816463/1000000000000 : ℝ) (258683461169/500000000000 : ℝ) (517366922347/1000000000000 : ℝ) (258683461161/500000000000 : ℝ) (517366922331/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 4 (258683461169/500000000000 : ℝ) (517366922347/1000000000000 : ℝ) (258683461161/500000000000 : ℝ) (517366922331/1000000000000 : ℝ) (51736692233/100000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 5 (51736692233/100000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 6 (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8977/65536 : ℝ))) 7 (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8977/65536 : ℝ)) hmem 8 (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8977/65536 : ℝ))) hcmem 8 (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8977/65536 : ℝ)) (49514362751/50000000000 : ℝ) (990287255023/1000000000000 : ℝ) (517366922329/1000000000000 : ℝ) (517366922339/1000000000000 : ℝ) (205162203461/250000000000 : ℝ) (820648813863/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0366_exp_lower
  have heNumeric : (504753078253/250000000000 : ℝ)/4 ≤ Real.exp (-341842961619/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753078253/250000000000 : ℝ)/4 ≤ Real.exp ((561/4096 : ℝ)-(820648813863/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (561/4096 : ℝ) (8977/65536 : ℝ) (820648813863/1000000000000 : ℝ) (504753078253/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0367; no trusted numerical premise.
theorem cover7_leaf0367_exp_radius : (498778339459584851/500000000000000000 : ℝ) ≤ Real.exp ((-4489/229376 : ℝ)/8) ∧ Real.exp ((-4489/229376 : ℝ)/8) ≤ (997556678919169703/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4489/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0367_exp_lower : (57380574544621661/62500000000000000 : ℝ) ≤ Real.exp ((-10938973857567/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938973857567/16000000000000 : ℝ)/8) ≤ (918089192713946577/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938973857567/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0367_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506214189/500000000000 : ℝ) ≤ 4*Real.exp (8977/65536 : ℝ)*Real.exp (-mu (radius 7 (4489/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506214189/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4489/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0367_exp_radius
  have hrNumeric : (490309885959/500000000000 : ℝ) ≤ Real.exp (-4489/229376 : ℝ) ∧ Real.exp (-4489/229376 : ℝ) ≤ (980619771919/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490309885959/500000000000 : ℝ) ≤ (radius 7 (4489/32768 : ℝ)) ∧ (radius 7 (4489/32768 : ℝ)) ≤ (980619771919/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4489/32768 : ℝ)) (490309885959/500000000000 : ℝ) (980619771919/1000000000000 : ℝ) (7836822103/40000000000 : ℝ) (195920552581/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4489/32768 : ℝ)) (490309885959/500000000000 : ℝ) (980619771919/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490309885959/500000000000 : ℝ) (980619771919/1000000000000 : ℝ) (990309885959/1000000000000 : ℝ) (24757747149/25000000000 : ℝ) (495131238137/500000000000 : ℝ) (247565619069/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 1 (990309885959/1000000000000 : ℝ) (24757747149/25000000000 : ℝ) (495131238137/500000000000 : ℝ) (247565619069/250000000000 : ℝ) (247571545279/250000000000 : ℝ) (495143090559/500000000000 : ℝ) (30946443151/31250000000 : ℝ) (198057236167/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 2 (247571545279/250000000000 : ℝ) (495143090559/500000000000 : ℝ) (30946443151/31250000000 : ℝ) (198057236167/200000000000 : ℝ) (495143090487/500000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 3 (495143090487/500000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 4 (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 5 (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 6 (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4489/32768 : ℝ)) 7 (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4489/32768 : ℝ))) (7836822103/40000000000 : ℝ) (195920552581/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7836822103/40000000000 : ℝ) (195920552581/1000000000000 : ℝ) (597960276287/1000000000000 : ℝ) (597960276291/1000000000000 : ℝ) (13832160519/31250000000 : ℝ) (55328642077/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 1 (597960276287/1000000000000 : ℝ) (597960276291/1000000000000 : ℝ) (13832160519/31250000000 : ℝ) (55328642077/125000000000 : ℝ) (520294706447/1000000000000 : ℝ) (260147353227/500000000000 : ℝ) (514465393217/1000000000000 : ℝ) (20578615729/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 2 (520294706447/1000000000000 : ℝ) (260147353227/500000000000 : ℝ) (514465393217/1000000000000 : ℝ) (20578615729/40000000000 : ℝ) (64672506229/125000000000 : ℝ) (6467250623/12500000000 : ℝ) (258685919959/500000000000 : ℝ) (517371839927/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 3 (64672506229/125000000000 : ℝ) (6467250623/12500000000 : ℝ) (258685919959/500000000000 : ℝ) (517371839927/1000000000000 : ℝ) (4139007559/8000000000 : ℝ) (129343986221/250000000000 : ℝ) (258687972429/500000000000 : ℝ) (129343986217/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 4 (4139007559/8000000000 : ℝ) (129343986221/250000000000 : ℝ) (258687972429/500000000000 : ℝ) (129343986217/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 5 (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 6 (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4489/32768 : ℝ))) 7 (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4489/32768 : ℝ)) hmem 8 (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4489/32768 : ℝ))) hcmem 8 (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4489/32768 : ℝ)) (990286180973/1000000000000 : ℝ) (990286180977/1000000000000 : ℝ) (258687972433/500000000000 : ℝ) (129343986219/250000000000 : ℝ) (205166003873/250000000000 : ℝ) (102583001939/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0367_exp_lower
  have heNumeric : (1009506214189/500000000000 : ℝ)/4 ≤ Real.exp (-10938973857567/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506214189/500000000000 : ℝ)/4 ≤ Real.exp ((8977/65536 : ℝ)-(102583001939/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8977/65536 : ℝ) (4489/32768 : ℝ) (102583001939/125000000000 : ℝ) (1009506214189/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0368; no trusted numerical premise.
theorem cover7_leaf0368_exp_radius : (498778203553291389/500000000000000000 : ℝ) ≤ Real.exp ((-8979/458752 : ℝ)/8) ∧ Real.exp ((-8979/458752 : ℝ)/8) ≤ (997556407106582779/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8979/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0368_exp_lower : (114761149925207467/125000000000000000 : ℝ) ≤ Real.exp ((-5469486462583/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469486462583/8000000000000 : ℝ)/8) ≤ (918089199401659737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469486462583/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0368_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753136509/250000000000 : ℝ) ≤ 4*Real.exp (4489/32768 : ℝ)*Real.exp (-mu (radius 7 (8979/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504753136509/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8979/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0368_exp_radius
  have hrNumeric : (980617634339/1000000000000 : ℝ) ≤ Real.exp (-8979/458752 : ℝ) ∧ Real.exp (-8979/458752 : ℝ) ≤ (49030881717/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980617634339/1000000000000 : ℝ) ≤ (radius 7 (8979/65536 : ℝ)) ∧ (radius 7 (8979/65536 : ℝ)) ≤ (49030881717/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8979/65536 : ℝ)) (980617634339/1000000000000 : ℝ) (49030881717/50000000000 : ℝ) (97965625631/500000000000 : ℝ) (48982812817/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8979/65536 : ℝ)) (980617634339/1000000000000 : ℝ) (49030881717/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980617634339/1000000000000 : ℝ) (49030881717/50000000000 : ℝ) (990308817169/1000000000000 : ℝ) (99030881717/100000000000 : ℝ) (39610455879/40000000000 : ℝ) (61891337311/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 1 (990308817169/1000000000000 : ℝ) (99030881717/100000000000 : ℝ) (39610455879/40000000000 : ℝ) (61891337311/62500000000 : ℝ) (7736602399/7812500000 : ℝ) (990285107073/1000000000000 : ℝ) (247571276697/250000000000 : ℝ) (99028510679/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 2 (7736602399/7812500000 : ℝ) (990285107073/1000000000000 : ℝ) (247571276697/250000000000 : ℝ) (99028510679/100000000000 : ℝ) (99028510693/100000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 3 (99028510693/100000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 4 (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 5 (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 6 (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8979/65536 : ℝ)) 7 (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8979/65536 : ℝ))) (97965625631/500000000000 : ℝ) (48982812817/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97965625631/500000000000 : ℝ) (48982812817/250000000000 : ℝ) (597965625631/1000000000000 : ℝ) (298982812817/500000000000 : ℝ) (110660305457/250000000000 : ℝ) (110660305459/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 1 (597965625631/1000000000000 : ℝ) (298982812817/500000000000 : ℝ) (110660305457/250000000000 : ℝ) (110660305459/250000000000 : ℝ) (520303423729/1000000000000 : ℝ) (104060684747/200000000000 : ℝ) (64309339711/125000000000 : ℝ) (102894943539/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 2 (520303423729/1000000000000 : ℝ) (104060684747/200000000000 : ℝ) (64309339711/125000000000 : ℝ) (102894943539/200000000000 : ℝ) (129347267677/250000000000 : ℝ) (103477814143/200000000000 : ℝ) (64672607831/125000000000 : ℝ) (8084075979/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 3 (129347267677/250000000000 : ℝ) (103477814143/200000000000 : ℝ) (64672607831/125000000000 : ℝ) (8084075979/15625000000 : ℝ) (258692483339/500000000000 : ℝ) (258692483343/500000000000 : ℝ) (517384966661/1000000000000 : ℝ) (51738496667/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 4 (258692483339/500000000000 : ℝ) (258692483343/500000000000 : ℝ) (517384966661/1000000000000 : ℝ) (51738496667/100000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 5 (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 6 (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8979/65536 : ℝ))) 7 (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8979/65536 : ℝ)) hmem 8 (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8979/65536 : ℝ))) hcmem 8 (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8979/65536 : ℝ)) (990285106929/1000000000000 : ℝ) (247571276733/250000000000 : ℝ) (517384966669/1000000000000 : ℝ) (258692483339/500000000000 : ℝ) (820679216009/1000000000000 : ℝ) (410339608013/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0368_exp_lower
  have heNumeric : (504753136509/250000000000 : ℝ)/4 ≤ Real.exp (-5469486462583/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753136509/250000000000 : ℝ)/4 ≤ Real.exp ((4489/32768 : ℝ)-(410339608013/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4489/32768 : ℝ) (8979/65536 : ℝ) (410339608013/500000000000 : ℝ) (504753136509/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0369; no trusted numerical premise.
theorem cover7_leaf0369_exp_radius : (997556135294069917/1000000000000000000 : ℝ) ≤ Real.exp ((-2245/114688 : ℝ)/8) ∧ Real.exp ((-2245/114688 : ℝ)/8) ≤ (498778067647034959/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2245/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0369_exp_lower : (229522301554533739/250000000000000000 : ℝ) ≤ Real.exp ((-10938971974813/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938971974813/16000000000000 : ℝ)/8) ≤ (918089206218134957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938971974813/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0369_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475316649/25000000000 : ℝ) ≤ 4*Real.exp (8979/65536 : ℝ)*Real.exp (-mu (radius 7 (2245/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (50475316649/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2245/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0369_exp_radius
  have hrNumeric : (245153874191/250000000000 : ℝ) ≤ Real.exp (-2245/114688 : ℝ) ∧ Real.exp (-2245/114688 : ℝ) ≤ (196123099353/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245153874191/250000000000 : ℝ) ≤ (radius 7 (2245/16384 : ℝ)) ∧ (radius 7 (2245/16384 : ℝ)) ≤ (196123099353/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2245/16384 : ℝ)) (245153874191/250000000000 : ℝ) (196123099353/200000000000 : ℝ) (97970974661/500000000000 : ℝ) (12246371833/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2245/16384 : ℝ)) (245153874191/250000000000 : ℝ) (196123099353/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245153874191/250000000000 : ℝ) (196123099353/200000000000 : ℝ) (495153874191/500000000000 : ℝ) (990307748383/1000000000000 : ℝ) (247565079419/250000000000 : ℝ) (990260317677/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 1 (495153874191/500000000000 : ℝ) (990307748383/1000000000000 : ℝ) (247565079419/250000000000 : ℝ) (990260317677/1000000000000 : ℝ) (990284033029/1000000000000 : ℝ) (99028403303/100000000000 : ℝ) (198056806549/200000000000 : ℝ) (990284032747/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 2 (990284033029/1000000000000 : ℝ) (99028403303/100000000000 : ℝ) (198056806549/200000000000 : ℝ) (990284032747/1000000000000 : ℝ) (990284032887/1000000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 3 (990284032887/1000000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 4 (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 5 (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 6 (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2245/16384 : ℝ)) 7 (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2245/16384 : ℝ))) (97970974661/500000000000 : ℝ) (12246371833/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97970974661/500000000000 : ℝ) (12246371833/62500000000 : ℝ) (597970974661/1000000000000 : ℝ) (74746371833/125000000000 : ℝ) (44265330601/100000000000 : ℝ) (221326653009/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 1 (597970974661/1000000000000 : ℝ) (74746371833/125000000000 : ℝ) (44265330601/100000000000 : ℝ) (221326653009/500000000000 : ℝ) (104062428067/200000000000 : ℝ) (520312140341/1000000000000 : ℝ) (514484041377/1000000000000 : ℝ) (64310505173/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 2 (104062428067/200000000000 : ℝ) (520312140341/1000000000000 : ℝ) (514484041377/1000000000000 : ℝ) (64310505173/125000000000 : ℝ) (64674761357/125000000000 : ℝ) (517398090863/1000000000000 : ℝ) (64673735581/125000000000 : ℝ) (32336867791/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 3 (64674761357/125000000000 : ℝ) (517398090863/1000000000000 : ℝ) (64673735581/125000000000 : ℝ) (32336867791/62500000000 : ℝ) (64674248469/125000000000 : ℝ) (6467424847/12500000000 : ℝ) (103478797547/200000000000 : ℝ) (16168562117/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 4 (64674248469/125000000000 : ℝ) (6467424847/12500000000 : ℝ) (103478797547/200000000000 : ℝ) (16168562117/31250000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 5 (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 6 (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2245/16384 : ℝ))) 7 (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2245/16384 : ℝ)) hmem 8 (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2245/16384 : ℝ))) hcmem 8 (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2245/16384 : ℝ)) (495142016443/500000000000 : ℝ) (990284032889/1000000000000 : ℝ) (517393987743/1000000000000 : ℝ) (64674248469/125000000000 : ℝ) (4103472077/5000000000 : ℝ) (410347207709/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0369_exp_lower
  have heNumeric : (50475316649/25000000000 : ℝ)/4 ≤ Real.exp (-10938971974813/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475316649/25000000000 : ℝ)/4 ≤ Real.exp ((8979/65536 : ℝ)-(410347207709/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8979/65536 : ℝ) (2245/16384 : ℝ) (410347207709/500000000000 : ℝ) (50475316649/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0370; no trusted numerical premise.
theorem cover7_leaf0370_exp_radius : (997555863481631119/1000000000000000000 : ℝ) ≤ Real.exp ((-1283/65536 : ℝ)/8) ∧ Real.exp ((-1283/65536 : ℝ)/8) ≤ (12469448293520389/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1283/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0370_exp_lower : (918089213164634611/1000000000000000000 : ℝ) ≤ Real.exp ((-2734742751583/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734742751583/4000000000000 : ℝ)/8) ≤ (229522303291158653/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734742751583/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0370_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012788171/1000000000000 : ℝ) ≤ 4*Real.exp (2245/16384 : ℝ)*Real.exp (-mu (radius 7 (8981/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012788171/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8981/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0370_exp_radius
  have hrNumeric : (490306679597/500000000000 : ℝ) ≤ Real.exp (-1283/65536 : ℝ) ∧ Real.exp (-1283/65536 : ℝ) ≤ (196122671839/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490306679597/500000000000 : ℝ) ≤ (radius 7 (8981/65536 : ℝ)) ∧ (radius 7 (8981/65536 : ℝ)) ≤ (196122671839/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8981/65536 : ℝ)) (490306679597/500000000000 : ℝ) (196122671839/200000000000 : ℝ) (195952646749/1000000000000 : ℝ) (39190529351/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8981/65536 : ℝ)) (490306679597/500000000000 : ℝ) (196122671839/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490306679597/500000000000 : ℝ) (196122671839/200000000000 : ℝ) (990306679597/1000000000000 : ℝ) (495153339799/500000000000 : ℝ) (495129619189/500000000000 : ℝ) (49512961919/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 1 (990306679597/1000000000000 : ℝ) (495153339799/500000000000 : ℝ) (495129619189/500000000000 : ℝ) (49512961919/50000000000 : ℝ) (990282958987/1000000000000 : ℝ) (990282958989/1000000000000 : ℝ) (990282958703/1000000000000 : ℝ) (198056591741/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 2 (990282958987/1000000000000 : ℝ) (990282958989/1000000000000 : ℝ) (990282958703/1000000000000 : ℝ) (198056591741/200000000000 : ℝ) (198056591769/200000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 3 (198056591769/200000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 4 (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 5 (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 6 (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8981/65536 : ℝ)) 7 (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8981/65536 : ℝ))) (195952646749/1000000000000 : ℝ) (39190529351/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195952646749/1000000000000 : ℝ) (39190529351/200000000000 : ℝ) (298988161687/500000000000 : ℝ) (298988161689/500000000000 : ℝ) (442665389147/1000000000000 : ℝ) (88533077831/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 1 (298988161687/500000000000 : ℝ) (298988161689/500000000000 : ℝ) (442665389147/1000000000000 : ℝ) (88533077831/200000000000 : ℝ) (26016042813/50000000000 : ℝ) (520320856267/1000000000000 : ℝ) (257246682139/500000000000 : ℝ) (257246682143/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 2 (26016042813/50000000000 : ℝ) (520320856267/1000000000000 : ℝ) (257246682139/500000000000 : ℝ) (257246682143/500000000000 : ℝ) (517407110269/1000000000000 : ℝ) (517407110277/1000000000000 : ℝ) (258699452957/500000000000 : ℝ) (258699452961/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 3 (517407110269/1000000000000 : ℝ) (517407110277/1000000000000 : ℝ) (258699452957/500000000000 : ℝ) (258699452961/500000000000 : ℝ) (517403008091/1000000000000 : ℝ) (5174030081/10000000000 : ℝ) (20696120323/40000000000 : ℝ) (129350752021/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 4 (517403008091/1000000000000 : ℝ) (5174030081/10000000000 : ℝ) (20696120323/40000000000 : ℝ) (129350752021/250000000000 : ℝ) (517403008083/1000000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 5 (517403008083/1000000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 6 (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8981/65536 : ℝ))) 7 (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8981/65536 : ℝ)) hmem 8 (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8981/65536 : ℝ))) hcmem 8 (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8981/65536 : ℝ)) (247570739711/250000000000 : ℝ) (990282958847/1000000000000 : ℝ) (258701504041/500000000000 : ℝ) (129350752023/250000000000 : ℝ) (410354806829/500000000000 : ℝ) (820709613677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0370_exp_lower
  have heNumeric : (2019012788171/1000000000000 : ℝ)/4 ≤ Real.exp (-2734742751583/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012788171/1000000000000 : ℝ)/4 ≤ Real.exp ((2245/16384 : ℝ)-(820709613677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2245/16384 : ℝ) (8981/65536 : ℝ) (820709613677/1000000000000 : ℝ) (2019012788171/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0371; no trusted numerical premise.
theorem cover7_leaf0371_exp_radius : (62347224479329149/62500000000000000 : ℝ) ≤ Real.exp ((-4491/229376 : ℝ)/8) ∧ Real.exp ((-4491/229376 : ℝ)/8) ≤ (199511118333853277/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4491/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0371_exp_lower : (183617844048231741/200000000000000000 : ℝ) ≤ Real.exp ((-10938970019723/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938970019723/16000000000000 : ℝ)/8) ≤ (459044610120579353/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938970019723/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0371_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012912669/1000000000000 : ℝ) ≤ 4*Real.exp (8981/65536 : ℝ)*Real.exp (-mu (radius 7 (4491/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012912669/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4491/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0371_exp_radius
  have hrNumeric : (980611221629/1000000000000 : ℝ) ≤ Real.exp (-4491/229376 : ℝ) ∧ Real.exp (-4491/229376 : ℝ) ≤ (98061122163/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980611221629/1000000000000 : ℝ) ≤ (radius 7 (4491/32768 : ℝ)) ∧ (radius 7 (4491/32768 : ℝ)) ≤ (98061122163/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4491/32768 : ℝ)) (980611221629/1000000000000 : ℝ) (98061122163/100000000000 : ℝ) (24495417943/125000000000 : ℝ) (3919266871/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4491/32768 : ℝ)) (980611221629/1000000000000 : ℝ) (98061122163/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980611221629/1000000000000 : ℝ) (98061122163/100000000000 : ℝ) (495152805407/500000000000 : ℝ) (198061122163/200000000000 : ℝ) (495129079541/500000000000 : ℝ) (990258159083/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 1 (495152805407/500000000000 : ℝ) (198061122163/200000000000 : ℝ) (495129079541/500000000000 : ℝ) (990258159083/1000000000000 : ℝ) (247570471237/250000000000 : ℝ) (990281884949/1000000000000 : ℝ) (990281884663/1000000000000 : ℝ) (198056376933/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 2 (247570471237/250000000000 : ℝ) (990281884949/1000000000000 : ℝ) (990281884663/1000000000000 : ℝ) (198056376933/200000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 3 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 4 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 5 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 6 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4491/32768 : ℝ)) 7 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4491/32768 : ℝ))) (24495417943/125000000000 : ℝ) (3919266871/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24495417943/125000000000 : ℝ) (3919266871/20000000000 : ℝ) (149495417943/250000000000 : ℝ) (23919266871/40000000000 : ℝ) (11066936781/25000000000 : ℝ) (27667341953/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 1 (149495417943/250000000000 : ℝ) (23919266871/40000000000 : ℝ) (11066936781/25000000000 : ℝ) (27667341953/62500000000 : ℝ) (260164785753/500000000000 : ℝ) (65041196439/125000000000 : ℝ) (102900537279/200000000000 : ℝ) (257251343201/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 2 (260164785753/500000000000 : ℝ) (65041196439/125000000000 : ℝ) (102900537279/200000000000 : ℝ) (257251343201/500000000000 : ℝ) (10348322579/20000000000 : ℝ) (517416128957/1000000000000 : ℝ) (517407926447/1000000000000 : ℝ) (258703963227/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 3 (10348322579/20000000000 : ℝ) (517416128957/1000000000000 : ℝ) (517407926447/1000000000000 : ℝ) (258703963227/500000000000 : ℝ) (258706013849/500000000000 : ℝ) (258706013853/500000000000 : ℝ) (258706013841/500000000000 : ℝ) (51741202769/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 4 (258706013849/500000000000 : ℝ) (258706013853/500000000000 : ℝ) (258706013841/500000000000 : ℝ) (51741202769/100000000000 : ℝ) (51741202769/100000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 5 (51741202769/100000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 6 (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4491/32768 : ℝ))) 7 (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4491/32768 : ℝ)) hmem 8 (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4491/32768 : ℝ))) hcmem 8 (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4491/32768 : ℝ)) (198056376961/200000000000 : ℝ) (990281884807/1000000000000 : ℝ) (517412027689/1000000000000 : ℝ) (258706013849/500000000000 : ℝ) (410362405393/500000000000 : ℝ) (820724810803/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0371_exp_lower
  have heNumeric : (2019012912669/1000000000000 : ℝ)/4 ≤ Real.exp (-10938970019723/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012912669/1000000000000 : ℝ)/4 ≤ Real.exp ((8981/65536 : ℝ)-(820724810803/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8981/65536 : ℝ) (4491/32768 : ℝ) (820724810803/1000000000000 : ℝ) (2019012912669/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0372; no trusted numerical premise.
theorem cover7_leaf0372_exp_radius : (31173603745530491/31250000000000000 : ℝ) ≤ Real.exp ((-8983/458752 : ℝ)/8) ∧ Real.exp ((-8983/458752 : ℝ)/8) ≤ (997555319856975713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8983/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0372_exp_lower : (918089227447362957/1000000000000000000 : ℝ) ≤ Real.exp ((-5469484507517/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469484507517/8000000000000 : ℝ)/8) ≤ (459044613723681479/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469484507517/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0372_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013039449/1000000000000 : ℝ) ≤ 4*Real.exp (4491/32768 : ℝ)*Real.exp (-mu (radius 7 (8983/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013039449/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8983/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0372_exp_radius
  have hrNumeric : (980609084069/1000000000000 : ℝ) ≤ Real.exp (-8983/458752 : ℝ) ∧ Real.exp (-8983/458752 : ℝ) ≤ (98060908407/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980609084069/1000000000000 : ℝ) ≤ (radius 7 (8983/65536 : ℝ)) ∧ (radius 7 (8983/65536 : ℝ)) ≤ (98060908407/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8983/65536 : ℝ)) (980609084069/1000000000000 : ℝ) (98060908407/100000000000 : ℝ) (195974039707/1000000000000 : ℝ) (195974039713/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8983/65536 : ℝ)) (980609084069/1000000000000 : ℝ) (98060908407/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980609084069/1000000000000 : ℝ) (98060908407/100000000000 : ℝ) (495152271017/500000000000 : ℝ) (198060908407/200000000000 : ℝ) (990257079787/1000000000000 : ℝ) (247564269947/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 1 (495152271017/500000000000 : ℝ) (198060908407/200000000000 : ℝ) (990257079787/1000000000000 : ℝ) (247564269947/250000000000 : ℝ) (99028081091/100000000000 : ℝ) (30946275341/31250000000 : ℝ) (495140405313/500000000000 : ℝ) (247570202657/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 2 (99028081091/100000000000 : ℝ) (30946275341/31250000000 : ℝ) (495140405313/500000000000 : ℝ) (247570202657/250000000000 : ℝ) (61892550673/62500000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 3 (61892550673/62500000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 4 (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 5 (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 6 (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8983/65536 : ℝ)) 7 (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8983/65536 : ℝ))) (195974039707/1000000000000 : ℝ) (195974039713/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195974039707/1000000000000 : ℝ) (195974039713/1000000000000 : ℝ) (597987019853/1000000000000 : ℝ) (597987019857/1000000000000 : ℝ) (44268955229/100000000000 : ℝ) (221344776149/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 1 (597987019853/1000000000000 : ℝ) (597987019857/1000000000000 : ℝ) (44268955229/100000000000 : ℝ) (221344776149/500000000000 : ℝ) (520338286071/1000000000000 : ℝ) (260169143039/500000000000 : ℝ) (20580480309/40000000000 : ℝ) (514512007733/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 2 (520338286071/1000000000000 : ℝ) (260169143039/500000000000 : ℝ) (20580480309/40000000000 : ℝ) (514512007733/1000000000000 : ℝ) (258712573449/500000000000 : ℝ) (258712573453/500000000000 : ℝ) (258708473123/500000000000 : ℝ) (258708473127/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 3 (258712573449/500000000000 : ℝ) (258712573453/500000000000 : ℝ) (258708473123/500000000000 : ℝ) (258708473127/500000000000 : ℝ) (129355261643/250000000000 : ℝ) (25871052329/50000000000 : ℝ) (103484209311/200000000000 : ℝ) (129355261641/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 4 (129355261643/250000000000 : ℝ) (25871052329/50000000000 : ℝ) (103484209311/200000000000 : ℝ) (129355261641/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 5 (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 6 (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8983/65536 : ℝ))) 7 (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8983/65536 : ℝ)) hmem 8 (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8983/65536 : ℝ))) hcmem 8 (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8983/65536 : ℝ)) (990280810767/1000000000000 : ℝ) (99028081077/100000000000 : ℝ) (517421046563/1000000000000 : ℝ) (129355261643/250000000000 : ℝ) (410370003391/500000000000 : ℝ) (820740006799/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0372_exp_lower
  have heNumeric : (2019013039449/1000000000000 : ℝ)/4 ≤ Real.exp (-5469484507517/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013039449/1000000000000 : ℝ)/4 ≤ Real.exp ((4491/32768 : ℝ)-(820740006799/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4491/32768 : ℝ) (8983/65536 : ℝ) (820740006799/1000000000000 : ℝ) (2019013039449/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0373; no trusted numerical premise.
theorem cover7_leaf0373_exp_radius : (997555048044759103/1000000000000000000 : ℝ) ≤ Real.exp ((-1123/57344 : ℝ)/8) ∧ Real.exp ((-1123/57344 : ℝ)/8) ≤ (15586797625699361/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1123/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0373_exp_lower : (36723569391311533/40000000000000000 : ℝ) ≤ Real.exp ((-10938967992329/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938967992329/16000000000000 : ℝ)/8) ≤ (459044617391394163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938967992329/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0373_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013168503/1000000000000 : ℝ) ≤ 4*Real.exp (8983/65536 : ℝ)*Real.exp (-mu (radius 7 (1123/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013168503/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1123/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0373_exp_radius
  have hrNumeric : (980606946513/1000000000000 : ℝ) ≤ Real.exp (-1123/57344 : ℝ) ∧ Real.exp (-1123/57344 : ℝ) ≤ (490303473257/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980606946513/1000000000000 : ℝ) ≤ (radius 7 (1123/8192 : ℝ)) ∧ (radius 7 (1123/8192 : ℝ)) ≤ (490303473257/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1123/8192 : ℝ)) (980606946513/1000000000000 : ℝ) (490303473257/500000000000 : ℝ) (195984735243/1000000000000 : ℝ) (195984735249/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1123/8192 : ℝ)) (980606946513/1000000000000 : ℝ) (490303473257/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980606946513/1000000000000 : ℝ) (490303473257/500000000000 : ℝ) (123787934157/125000000000 : ℝ) (990303473257/1000000000000 : ℝ) (990256000493/1000000000000 : ℝ) (495128000247/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 1 (123787934157/125000000000 : ℝ) (990303473257/1000000000000 : ℝ) (990256000493/1000000000000 : ℝ) (495128000247/500000000000 : ℝ) (495139868437/500000000000 : ℝ) (247569934219/250000000000 : ℝ) (99027973659/100000000000 : ℝ) (61892483537/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 2 (495139868437/500000000000 : ℝ) (247569934219/250000000000 : ℝ) (99027973659/100000000000 : ℝ) (61892483537/62500000000 : ℝ) (247569934183/250000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 3 (247569934183/250000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 4 (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 5 (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 6 (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1123/8192 : ℝ)) 7 (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1123/8192 : ℝ))) (195984735243/1000000000000 : ℝ) (195984735249/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195984735243/1000000000000 : ℝ) (195984735249/1000000000000 : ℝ) (597992367621/1000000000000 : ℝ) (4783938941/8000000000 : ℝ) (221350816151/500000000000 : ℝ) (442701632309/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 1 (597992367621/1000000000000 : ℝ) (4783938941/8000000000 : ℝ) (221350816151/500000000000 : ℝ) (442701632309/1000000000000 : ℝ) (520346999961/1000000000000 : ℝ) (520346999967/1000000000000 : ℝ) (20580853131/40000000000 : ℝ) (514521328281/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 2 (520346999961/1000000000000 : ℝ) (520346999967/1000000000000 : ℝ) (20580853131/40000000000 : ℝ) (514521328281/1000000000000 : ℝ) (258717082059/500000000000 : ℝ) (129358541031/250000000000 : ℝ) (129356491329/250000000000 : ℝ) (517425965323/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 3 (258717082059/500000000000 : ℝ) (129358541031/250000000000 : ℝ) (129356491329/250000000000 : ℝ) (517425965323/1000000000000 : ℝ) (517430064717/1000000000000 : ℝ) (129357516181/250000000000 : ℝ) (5174300647/10000000000 : ℝ) (129357516177/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 4 (517430064717/1000000000000 : ℝ) (129357516181/250000000000 : ℝ) (5174300647/10000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 5 (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 6 (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1123/8192 : ℝ))) 7 (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1123/8192 : ℝ)) hmem 8 (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1123/8192 : ℝ))) hcmem 8 (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1123/8192 : ℝ)) (990279736731/1000000000000 : ℝ) (495139868367/500000000000 : ℝ) (129357516177/250000000000 : ℝ) (129357516179/250000000000 : ℝ) (820755201653/1000000000000 : ℝ) (820755201669/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0373_exp_lower
  have heNumeric : (2019013168503/1000000000000 : ℝ)/4 ≤ Real.exp (-10938967992329/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013168503/1000000000000 : ℝ)/4 ≤ Real.exp ((8983/65536 : ℝ)-(820755201669/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8983/65536 : ℝ) (1123/8192 : ℝ) (820755201669/1000000000000 : ℝ) (2019013168503/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0374; no trusted numerical premise.
theorem cover7_leaf0374_exp_radius : (249388694058154139/250000000000000000 : ℝ) ≤ Real.exp ((-8985/458752 : ℝ)/8) ∧ Real.exp ((-8985/458752 : ℝ)/8) ≤ (997554776232616557/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8985/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0374_exp_lower : (183617848449532867/200000000000000000 : ℝ) ≤ Real.exp ((-1367370868947/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367370868947/2000000000000 : ℝ)/8) ≤ (57380577640479021/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367370868947/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0374_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506649917/500000000000 : ℝ) ≤ 4*Real.exp (1123/8192 : ℝ)*Real.exp (-mu (radius 7 (8985/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506649917/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8985/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0374_exp_radius
  have hrNumeric : (490302404481/500000000000 : ℝ) ≤ Real.exp (-8985/458752 : ℝ) ∧ Real.exp (-8985/458752 : ℝ) ≤ (980604808963/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490302404481/500000000000 : ℝ) ≤ (radius 7 (8985/65536 : ℝ)) ∧ (radius 7 (8985/65536 : ℝ)) ≤ (980604808963/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8985/65536 : ℝ)) (490302404481/500000000000 : ℝ) (980604808963/1000000000000 : ℝ) (195995430147/1000000000000 : ℝ) (195995430153/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8985/65536 : ℝ)) (490302404481/500000000000 : ℝ) (980604808963/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490302404481/500000000000 : ℝ) (980604808963/1000000000000 : ℝ) (990302404481/1000000000000 : ℝ) (495151202241/500000000000 : ℝ) (2475637303/2500000000 : ℝ) (495127460601/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 1 (990302404481/1000000000000 : ℝ) (495151202241/500000000000 : ℝ) (2475637303/2500000000 : ℝ) (495127460601/500000000000 : ℝ) (24756966571/25000000000 : ℝ) (495139331421/500000000000 : ℝ) (198055732511/200000000000 : ℝ) (495139331279/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 2 (24756966571/25000000000 : ℝ) (495139331421/500000000000 : ℝ) (198055732511/200000000000 : ℝ) (495139331279/500000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 3 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 4 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 5 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 6 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8985/65536 : ℝ)) 7 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8985/65536 : ℝ))) (195995430147/1000000000000 : ℝ) (195995430153/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195995430147/1000000000000 : ℝ) (195995430153/1000000000000 : ℝ) (597997715073/1000000000000 : ℝ) (597997715077/1000000000000 : ℝ) (44271371127/100000000000 : ℝ) (221356855639/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 1 (597997715073/1000000000000 : ℝ) (597997715077/1000000000000 : ℝ) (44271371127/100000000000 : ℝ) (221356855639/500000000000 : ℝ) (520355713171/1000000000000 : ℝ) (260177856589/500000000000 : ℝ) (257265324019/500000000000 : ℝ) (102906129609/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 2 (520355713171/1000000000000 : ℝ) (260177856589/500000000000 : ℝ) (257265324019/500000000000 : ℝ) (102906129609/200000000000 : ℝ) (129360795151/250000000000 : ℝ) (129360795153/250000000000 : ℝ) (517434983653/1000000000000 : ℝ) (517434983661/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 3 (129360795151/250000000000 : ℝ) (129360795153/250000000000 : ℝ) (517434983653/1000000000000 : ℝ) (517434983661/1000000000000 : ℝ) (32339942633/62500000000 : ℝ) (517439082137/1000000000000 : ℝ) (4042492829/7812500000 : ℝ) (517439082121/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 4 (32339942633/62500000000 : ℝ) (517439082137/1000000000000 : ℝ) (4042492829/7812500000 : ℝ) (517439082121/1000000000000 : ℝ) (12935977053/25000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 5 (12935977053/25000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 6 (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8985/65536 : ℝ))) 7 (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8985/65536 : ℝ)) hmem 8 (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8985/65536 : ℝ))) hcmem 8 (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8985/65536 : ℝ)) (990278662697/1000000000000 : ℝ) (9902786627/10000000000 : ℝ) (517439082119/1000000000000 : ℝ) (517439082129/1000000000000 : ℝ) (3206134357/3906250000 : ℝ) (820770395411/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0374_exp_lower
  have heNumeric : (1009506649917/500000000000 : ℝ)/4 ≤ Real.exp (-1367370868947/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506649917/500000000000 : ℝ)/4 ≤ Real.exp ((1123/8192 : ℝ)-(820770395411/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1123/8192 : ℝ) (8985/65536 : ℝ) (820770395411/1000000000000 : ℝ) (1009506649917/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0350_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0350_certificate
#check SmaleRate.Proofs.cover7_leaf0351_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0351_certificate
#check SmaleRate.Proofs.cover7_leaf0352_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0352_certificate
#check SmaleRate.Proofs.cover7_leaf0353_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0353_certificate
#check SmaleRate.Proofs.cover7_leaf0354_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0354_certificate
#check SmaleRate.Proofs.cover7_leaf0355_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0355_certificate
#check SmaleRate.Proofs.cover7_leaf0356_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0356_certificate
#check SmaleRate.Proofs.cover7_leaf0357_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0357_certificate
#check SmaleRate.Proofs.cover7_leaf0358_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0358_certificate
#check SmaleRate.Proofs.cover7_leaf0359_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0359_certificate
#check SmaleRate.Proofs.cover7_leaf0360_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0360_certificate
#check SmaleRate.Proofs.cover7_leaf0361_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0361_certificate
#check SmaleRate.Proofs.cover7_leaf0362_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0362_certificate
#check SmaleRate.Proofs.cover7_leaf0363_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0363_certificate
#check SmaleRate.Proofs.cover7_leaf0364_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0364_certificate
#check SmaleRate.Proofs.cover7_leaf0365_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0365_certificate
#check SmaleRate.Proofs.cover7_leaf0366_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0366_certificate
#check SmaleRate.Proofs.cover7_leaf0367_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0367_certificate
#check SmaleRate.Proofs.cover7_leaf0368_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0368_certificate
#check SmaleRate.Proofs.cover7_leaf0369_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0369_certificate
#check SmaleRate.Proofs.cover7_leaf0370_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0370_certificate
#check SmaleRate.Proofs.cover7_leaf0371_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0371_certificate
#check SmaleRate.Proofs.cover7_leaf0372_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0372_certificate
#check SmaleRate.Proofs.cover7_leaf0373_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0373_certificate
#check SmaleRate.Proofs.cover7_leaf0374_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0374_certificate
