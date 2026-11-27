/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0250; no trusted numerical premise.
theorem cover7_leaf0250_exp_radius : (997588481503102529/1000000000000000000 : ℝ) ≤ Real.exp ((-8861/458752 : ℝ)/8) ∧ Real.exp ((-8861/458752 : ℝ)/8) ≤ (99758848150310253/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8861/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0250_exp_lower : (918089312334054647/1000000000000000000 : ℝ) ≤ Real.exp ((-2734739295033/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734739295033/4000000000000 : ℝ)/8) ≤ (114761164041756831/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734739295033/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0250_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753633219/250000000000 : ℝ) ≤ 4*Real.exp (2215/16384 : ℝ)*Real.exp (-mu (radius 7 (8861/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504753633219/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8861/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0250_exp_radius
  have hrNumeric : (245217475211/250000000000 : ℝ) ≤ Real.exp (-8861/458752 : ℝ) ∧ Real.exp (-8861/458752 : ℝ) ≤ (196173980169/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245217475211/250000000000 : ℝ) ≤ (radius 7 (8861/65536 : ℝ)) ∧ (radius 7 (8861/65536 : ℝ)) ≤ (196173980169/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8861/65536 : ℝ)) (245217475211/250000000000 : ℝ) (196173980169/200000000000 : ℝ) (12166526443/62500000000 : ℝ) (97332211547/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8861/65536 : ℝ)) (245217475211/250000000000 : ℝ) (196173980169/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245217475211/250000000000 : ℝ) (196173980169/200000000000 : ℝ) (495217475211/500000000000 : ℝ) (990434950423/1000000000000 : ℝ) (495194381239/500000000000 : ℝ) (12379859531/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 1 (495217475211/500000000000 : ℝ) (990434950423/1000000000000 : ℝ) (495194381239/500000000000 : ℝ) (12379859531/12500000000 : ℝ) (19808237129/20000000000 : ℝ) (247602964113/250000000000 : ℝ) (49520592809/50000000000 : ℝ) (990411856183/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 2 (19808237129/20000000000 : ℝ) (247602964113/250000000000 : ℝ) (49520592809/50000000000 : ℝ) (990411856183/1000000000000 : ℝ) (198082371263/200000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 3 (198082371263/200000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 4 (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 5 (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 6 (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8861/65536 : ℝ)) 7 (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8861/65536 : ℝ))) (12166526443/62500000000 : ℝ) (97332211547/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12166526443/62500000000 : ℝ) (97332211547/500000000000 : ℝ) (74666526443/125000000000 : ℝ) (597332211547/1000000000000 : ℝ) (441207913673/1000000000000 : ℝ) (441207913681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 1 (74666526443/125000000000 : ℝ) (597332211547/1000000000000 : ℝ) (441207913673/1000000000000 : ℝ) (441207913681/1000000000000 : ℝ) (32454378913/62500000000 : ℝ) (259635031307/500000000000 : ℝ) (12834224237/25000000000 : ℝ) (256684484743/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 2 (32454378913/62500000000 : ℝ) (259635031307/500000000000 : ℝ) (12834224237/25000000000 : ℝ) (256684484743/500000000000 : ℝ) (129079879011/250000000000 : ℝ) (10326390321/20000000000 : ℝ) (103262217083/200000000000 : ℝ) (258155542711/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 3 (129079879011/250000000000 : ℝ) (10326390321/20000000000 : ℝ) (103262217083/200000000000 : ℝ) (258155542711/500000000000 : ℝ) (516315300729/1000000000000 : ℝ) (4033713287/7812500000 : ℝ) (64539412589/125000000000 : ℝ) (516315300719/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 4 (516315300729/1000000000000 : ℝ) (4033713287/7812500000 : ℝ) (64539412589/125000000000 : ℝ) (516315300719/1000000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 5 (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 6 (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8861/65536 : ℝ))) 7 (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8861/65536 : ℝ)) hmem 8 (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8861/65536 : ℝ))) hcmem 8 (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8861/65536 : ℝ)) (495205928157/500000000000 : ℝ) (495205928159/500000000000 : ℝ) (6453941259/12500000000 : ℝ) (64539412591/125000000000 : ℝ) (163775538967/200000000000 : ℝ) (204719423713/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0250_exp_lower
  have heNumeric : (504753633219/250000000000 : ℝ)/4 ≤ Real.exp (-2734739295033/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753633219/250000000000 : ℝ)/4 ≤ Real.exp ((2215/16384 : ℝ)-(204719423713/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2215/16384 : ℝ) (8861/65536 : ℝ) (204719423713/250000000000 : ℝ) (504753633219/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0251; no trusted numerical premise.
theorem cover7_leaf0251_exp_radius : (99758820968185009/100000000000000000 : ℝ) ≤ Real.exp ((-633/32768 : ℝ)/8) ∧ Real.exp ((-633/32768 : ℝ)/8) ≤ (997588209681850091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-633/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0251_exp_lower : (229522325918689557/250000000000000000 : ℝ) ≤ Real.exp ((-10938958387411/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938958387411/16000000000000 : ℝ)/8) ≤ (918089303674758229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938958387411/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0251_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753595133/250000000000 : ℝ) ≤ 4*Real.exp (8861/65536 : ℝ)*Real.exp (-mu (radius 7 (4431/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504753595133/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4431/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0251_exp_radius
  have hrNumeric : (6130423517/6250000000 : ℝ) ≤ Real.exp (-633/32768 : ℝ) ∧ Real.exp (-633/32768 : ℝ) ≤ (980867762721/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (6130423517/6250000000 : ℝ) ≤ (radius 7 (4431/32768 : ℝ)) ∧ (radius 7 (4431/32768 : ℝ)) ≤ (980867762721/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4431/32768 : ℝ)) (6130423517/6250000000 : ℝ) (980867762721/1000000000000 : ℝ) (1946751963/10000000000 : ℝ) (97337598153/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4431/32768 : ℝ)) (6130423517/6250000000 : ℝ) (980867762721/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (6130423517/6250000000 : ℝ) (980867762721/1000000000000 : ℝ) (12380423517/12500000000 : ℝ) (990433881361/1000000000000 : ℝ) (990387683041/1000000000000 : ℝ) (495193841521/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 1 (12380423517/12500000000 : ℝ) (990433881361/1000000000000 : ℝ) (990387683041/1000000000000 : ℝ) (495193841521/500000000000 : ℝ) (4952053911/5000000000 : ℝ) (495205391101/500000000000 : ℝ) (990410781931/1000000000000 : ℝ) (990410781933/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 2 (4952053911/5000000000 : ℝ) (495205391101/500000000000 : ℝ) (990410781931/1000000000000 : ℝ) (990410781933/1000000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 3 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 4 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 5 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 6 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4431/32768 : ℝ)) 7 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4431/32768 : ℝ))) (1946751963/10000000000 : ℝ) (97337598153/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1946751963/10000000000 : ℝ) (97337598153/500000000000 : ℝ) (11946751963/20000000000 : ℝ) (597337598153/1000000000000 : ℝ) (220610061137/500000000000 : ℝ) (220610061141/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 1 (11946751963/20000000000 : ℝ) (597337598153/1000000000000 : ℝ) (220610061137/500000000000 : ℝ) (220610061141/500000000000 : ℝ) (129819715053/250000000000 : ℝ) (259639430109/500000000000 : ℝ) (513378386859/1000000000000 : ℝ) (256689193433/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 2 (129819715053/250000000000 : ℝ) (259639430109/500000000000 : ℝ) (513378386859/1000000000000 : ℝ) (256689193433/500000000000 : ℝ) (103265724707/200000000000 : ℝ) (258164311771/500000000000 : ℝ) (258160097413/500000000000 : ℝ) (516320194833/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 3 (103265724707/200000000000 : ℝ) (258164311771/500000000000 : ℝ) (258160097413/500000000000 : ℝ) (516320194833/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (129081102297/250000000000 : ℝ) (516324409163/1000000000000 : ℝ) (516324409171/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 4 (25816220459/50000000000 : ℝ) (129081102297/250000000000 : ℝ) (516324409163/1000000000000 : ℝ) (516324409171/1000000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 5 (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 6 (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4431/32768 : ℝ))) 7 (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4431/32768 : ℝ)) hmem 8 (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4431/32768 : ℝ))) hcmem 8 (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4431/32768 : ℝ)) (198082156413/200000000000 : ℝ) (247602695517/250000000000 : ℝ) (516324409171/1000000000000 : ℝ) (25816220459/50000000000 : ℝ) (818893029079/1000000000000 : ℝ) (102361628637/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0251_exp_lower
  have heNumeric : (504753595133/250000000000 : ℝ)/4 ≤ Real.exp (-10938958387411/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753595133/250000000000 : ℝ)/4 ≤ Real.exp ((8861/65536 : ℝ)-(102361628637/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8861/65536 : ℝ) (4431/32768 : ℝ) (102361628637/125000000000 : ℝ) (504753595133/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0252; no trusted numerical premise.
theorem cover7_leaf0252_exp_radius : (249396984465167929/250000000000000000 : ℝ) ≤ Real.exp ((-8863/458752 : ℝ)/8) ∧ Real.exp ((-8863/458752 : ℝ)/8) ≤ (997587937860671717/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8863/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0252_exp_lower : (183617859029464493/200000000000000000 : ℝ) ≤ Real.exp ((-5469479788153/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469479788153/8000000000000 : ℝ)/8) ≤ (459044647573661233/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469479788153/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0252_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014230507/1000000000000 : ℝ) ≤ 4*Real.exp (4431/32768 : ℝ)*Real.exp (-mu (radius 7 (8863/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014230507/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8863/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0252_exp_radius
  have hrNumeric : (4904328123/5000000000 : ℝ) ≤ Real.exp (-8863/458752 : ℝ) ∧ Real.exp (-8863/458752 : ℝ) ≤ (980865624601/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (4904328123/5000000000 : ℝ) ≤ (radius 7 (8863/65536 : ℝ)) ∧ (radius 7 (8863/65536 : ℝ)) ≤ (980865624601/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8863/65536 : ℝ)) (4904328123/5000000000 : ℝ) (980865624601/1000000000000 : ℝ) (194685968873/1000000000000 : ℝ) (194685968879/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8863/65536 : ℝ)) (4904328123/5000000000 : ℝ) (980865624601/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (4904328123/5000000000 : ℝ) (980865624601/1000000000000 : ℝ) (9904328123/10000000000 : ℝ) (990432812301/1000000000000 : ℝ) (247596650901/250000000000 : ℝ) (495193301803/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 1 (9904328123/10000000000 : ℝ) (990432812301/1000000000000 : ℝ) (247596650901/250000000000 : ℝ) (495193301803/500000000000 : ℝ) (61900606747/62500000000 : ℝ) (495204853977/500000000000 : ℝ) (495204853841/500000000000 : ℝ) (198081941537/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 2 (61900606747/62500000000 : ℝ) (495204853977/500000000000 : ℝ) (495204853841/500000000000 : ℝ) (198081941537/200000000000 : ℝ) (990409707817/1000000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 3 (990409707817/1000000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 4 (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 5 (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 6 (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8863/65536 : ℝ)) 7 (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8863/65536 : ℝ))) (194685968873/1000000000000 : ℝ) (194685968879/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194685968873/1000000000000 : ℝ) (194685968879/1000000000000 : ℝ) (149335746109/250000000000 : ℝ) (14933574611/25000000000 : ℝ) (441232329813/1000000000000 : ℝ) (441232329821/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 1 (149335746109/250000000000 : ℝ) (14933574611/25000000000 : ℝ) (441232329813/1000000000000 : ℝ) (441232329821/1000000000000 : ℝ) (129821914281/250000000000 : ℝ) (519287657131/1000000000000 : ℝ) (513387803439/1000000000000 : ℝ) (256693901723/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 2 (129821914281/250000000000 : ℝ) (519287657131/1000000000000 : ℝ) (513387803439/1000000000000 : ℝ) (256693901723/500000000000 : ℝ) (516337730281/1000000000000 : ℝ) (516337730289/1000000000000 : ℝ) (516329303491/1000000000000 : ℝ) (516329303499/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 3 (516337730281/1000000000000 : ℝ) (516337730289/1000000000000 : ℝ) (516329303491/1000000000000 : ℝ) (516329303499/1000000000000 : ℝ) (258166758443/500000000000 : ℝ) (258166758447/500000000000 : ℝ) (129083379217/250000000000 : ℝ) (516333516877/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 4 (258166758443/500000000000 : ℝ) (258166758447/500000000000 : ℝ) (129083379217/250000000000 : ℝ) (516333516877/1000000000000 : ℝ) (516333516877/1000000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 5 (516333516877/1000000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 6 (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8863/65536 : ℝ))) 7 (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8863/65536 : ℝ)) hmem 8 (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8863/65536 : ℝ))) hcmem 8 (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8863/65536 : ℝ)) (123801213477/125000000000 : ℝ) (49520485391/50000000000 : ℝ) (129083379219/250000000000 : ℝ) (258166758443/500000000000 : ℝ) (818908362171/1000000000000 : ℝ) (818908362191/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0252_exp_lower
  have heNumeric : (2019014230507/1000000000000 : ℝ)/4 ≤ Real.exp (-5469479788153/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014230507/1000000000000 : ℝ)/4 ≤ Real.exp ((4431/32768 : ℝ)-(818908362191/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4431/32768 : ℝ) (8863/65536 : ℝ) (818908362191/1000000000000 : ℝ) (2019014230507/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0253; no trusted numerical premise.
theorem cover7_leaf0253_exp_radius : (997587666039567407/1000000000000000000 : ℝ) ≤ Real.exp ((-277/14336 : ℝ)/8) ∧ Real.exp ((-277/14336 : ℝ)/8) ≤ (62349229127472963/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-277/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0253_exp_lower : (918089286752894967/1000000000000000000 : ℝ) ≤ Real.exp ((-10938960746657/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938960746657/16000000000000 : ℝ)/8) ≤ (114761160844111871/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938960746657/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0253_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009507041411/500000000000 : ℝ) ≤ 4*Real.exp (8863/65536 : ℝ)*Real.exp (-mu (radius 7 (277/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009507041411/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (277/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0253_exp_radius
  have hrNumeric : (196172697297/200000000000 : ℝ) ≤ Real.exp (-277/14336 : ℝ) ∧ Real.exp (-277/14336 : ℝ) ≤ (490431743243/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196172697297/200000000000 : ℝ) ≤ (radius 7 (277/2048 : ℝ)) ∧ (radius 7 (277/2048 : ℝ)) ≤ (490431743243/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (277/2048 : ℝ)) (196172697297/200000000000 : ℝ) (490431743243/500000000000 : ℝ) (121685463/625000000 : ℝ) (194696740807/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (277/2048 : ℝ)) (196172697297/200000000000 : ℝ) (490431743243/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (277/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196172697297/200000000000 : ℝ) (490431743243/500000000000 : ℝ) (495215871621/500000000000 : ℝ) (990431743243/1000000000000 : ℝ) (990385524169/1000000000000 : ℝ) (990385524171/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (277/2048 : ℝ)) 1 (495215871621/500000000000 : ℝ) (990431743243/1000000000000 : ℝ) (990385524169/1000000000000 : ℝ) (990385524171/1000000000000 : ℝ) (198081726741/200000000000 : ℝ) (990408633707/1000000000000 : ℝ) (198081726687/200000000000 : ℝ) (495204316719/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (277/2048 : ℝ)) 2 (198081726741/200000000000 : ℝ) (990408633707/1000000000000 : ℝ) (198081726687/200000000000 : ℝ) (495204316719/500000000000 : ℝ) (99040863357/100000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (277/2048 : ℝ)) 3 (99040863357/100000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (277/2048 : ℝ)) 4 (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (277/2048 : ℝ)) 5 (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (277/2048 : ℝ)) 6 (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (277/2048 : ℝ)) 7 (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (277/2048 : ℝ))) (121685463/625000000 : ℝ) (194696740807/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (121685463/625000000 : ℝ) (194696740807/1000000000000 : ℝ) (746685463/1250000000 : ℝ) (149337092601/250000000000 : ℝ) (441244536283/1000000000000 : ℝ) (110311134073/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 1 (746685463/1250000000 : ℝ) (149337092601/250000000000 : ℝ) (441244536283/1000000000000 : ℝ) (110311134073/250000000000 : ℝ) (519296453341/1000000000000 : ℝ) (129824113337/250000000000 : ℝ) (513397219213/1000000000000 : ℝ) (513397219221/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 2 (519296453341/1000000000000 : ℝ) (129824113337/250000000000 : ℝ) (513397219213/1000000000000 : ℝ) (513397219221/1000000000000 : ℝ) (516346836277/1000000000000 : ℝ) (103269367257/200000000000 : ℝ) (103267682281/200000000000 : ℝ) (516338411413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 3 (516346836277/1000000000000 : ℝ) (103269367257/200000000000 : ℝ) (103267682281/200000000000 : ℝ) (516338411413/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623849/1000000000000 : ℝ) (516342623823/1000000000000 : ℝ) (64542827979/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 4 (516342623841/1000000000000 : ℝ) (516342623849/1000000000000 : ℝ) (516342623823/1000000000000 : ℝ) (64542827979/125000000000 : ℝ) (64542827979/125000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 5 (64542827979/125000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 6 (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (277/2048 : ℝ))) 7 (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (277/2048 : ℝ)) hmem 8 (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (277/2048 : ℝ))) hcmem 8 (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (277/2048 : ℝ)) (990408633569/1000000000000 : ℝ) (990408633573/1000000000000 : ℝ) (516342623831/1000000000000 : ℝ) (516342623841/1000000000000 : ℝ) (818923694107/1000000000000 : ℝ) (818923694127/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0253_exp_lower
  have heNumeric : (1009507041411/500000000000 : ℝ)/4 ≤ Real.exp (-10938960746657/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009507041411/500000000000 : ℝ)/4 ≤ Real.exp ((8863/65536 : ℝ)-(818923694127/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8863/65536 : ℝ) (277/2048 : ℝ) (818923694127/1000000000000 : ℝ) (1009507041411/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0254; no trusted numerical premise.
theorem cover7_leaf0254_exp_radius : (249396848554634291/250000000000000000 : ℝ) ≤ Real.exp ((-8865/458752 : ℝ)/8) ∧ Real.exp ((-8865/458752 : ℝ)/8) ≤ (199517478843707433/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8865/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0254_exp_lower : (91808927849147573/100000000000000000 : ℝ) ≤ Real.exp ((-341842559327/500000000000 : ℝ)/8) ∧ Real.exp ((-341842559327/500000000000 : ℝ)/8) ≤ (918089278491475731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341842559327/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0254_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506968739/500000000000 : ℝ) ≤ 4*Real.exp (277/2048 : ℝ)*Real.exp (-mu (radius 7 (8865/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506968739/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8865/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0254_exp_radius
  have hrNumeric : (7846890787/8000000000 : ℝ) ≤ Real.exp (-8865/458752 : ℝ) ∧ Real.exp (-8865/458752 : ℝ) ≤ (122607668547/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7846890787/8000000000 : ℝ) ≤ (radius 7 (8865/65536 : ℝ)) ∧ (radius 7 (8865/65536 : ℝ)) ≤ (122607668547/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8865/65536 : ℝ)) (7846890787/8000000000 : ℝ) (122607668547/125000000000 : ℝ) (48676878021/250000000000 : ℝ) (19470751209/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8865/65536 : ℝ)) (7846890787/8000000000 : ℝ) (122607668547/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7846890787/8000000000 : ℝ) (122607668547/125000000000 : ℝ) (990430674187/1000000000000 : ℝ) (247607668547/250000000000 : ℝ) (198076888947/200000000000 : ℝ) (990384444737/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 1 (990430674187/1000000000000 : ℝ) (247607668547/250000000000 : ℝ) (198076888947/200000000000 : ℝ) (990384444737/1000000000000 : ℝ) (990407559461/1000000000000 : ℝ) (990407559463/1000000000000 : ℝ) (990407559191/1000000000000 : ℝ) (990407559193/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 2 (990407559461/1000000000000 : ℝ) (990407559463/1000000000000 : ℝ) (990407559191/1000000000000 : ℝ) (990407559193/1000000000000 : ℝ) (495203779663/500000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 3 (495203779663/500000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 4 (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 5 (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 6 (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8865/65536 : ℝ)) 7 (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8865/65536 : ℝ))) (48676878021/250000000000 : ℝ) (19470751209/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48676878021/250000000000 : ℝ) (19470751209/100000000000 : ℝ) (298676878021/500000000000 : ℝ) (119470751209/200000000000 : ℝ) (220628370843/500000000000 : ℝ) (220628370847/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 1 (298676878021/500000000000 : ℝ) (119470751209/200000000000 : ℝ) (220628370843/500000000000 : ℝ) (220628370847/500000000000 : ℝ) (16228289027/31250000000 : ℝ) (51930524887/100000000000 : ℝ) (64175829273/125000000000 : ℝ) (513406634191/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 2 (16228289027/31250000000 : ℝ) (51930524887/100000000000 : ℝ) (64175829273/125000000000 : ℝ) (513406634191/1000000000000 : ℝ) (129088985381/250000000000 : ℝ) (516355941531/1000000000000 : ℝ) (516347518569/1000000000000 : ℝ) (516347518577/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 3 (129088985381/250000000000 : ℝ) (516355941531/1000000000000 : ℝ) (516347518569/1000000000000 : ℝ) (516347518577/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (258175865027/500000000000 : ℝ) (516351730029/1000000000000 : ℝ) (516351730037/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 4 (258175865023/500000000000 : ℝ) (258175865027/500000000000 : ℝ) (516351730029/1000000000000 : ℝ) (516351730037/1000000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 5 (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 6 (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8865/65536 : ℝ))) 7 (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8865/65536 : ℝ)) hmem 8 (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8865/65536 : ℝ))) hcmem 8 (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8865/65536 : ℝ)) (39616302373/40000000000 : ℝ) (30950236229/31250000000 : ℝ) (516351730037/1000000000000 : ℝ) (258175865023/500000000000 : ℝ) (409469512443/500000000000 : ℝ) (102367378113/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0254_exp_lower
  have heNumeric : (1009506968739/500000000000 : ℝ)/4 ≤ Real.exp (-341842559327/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506968739/500000000000 : ℝ)/4 ≤ Real.exp ((277/2048 : ℝ)-(102367378113/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (277/2048 : ℝ) (8865/65536 : ℝ) (102367378113/125000000000 : ℝ) (1009506968739/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0255; no trusted numerical premise.
theorem cover7_leaf0255_exp_radius : (498793561198790493/500000000000000000 : ℝ) ≤ Real.exp ((-4433/229376 : ℝ)/8) ∧ Real.exp ((-4433/229376 : ℝ)/8) ≤ (997587122397580987/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4433/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0255_exp_lower : (918089270362146661/1000000000000000000 : ℝ) ≤ Real.exp ((-2187792606371/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187792606371/3200000000000 : ℝ)/8) ≤ (459044635181073331/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187792606371/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0255_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013794457/1000000000000 : ℝ) ≤ 4*Real.exp (8865/65536 : ℝ)*Real.exp (-mu (radius 7 (4433/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013794457/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4433/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0255_exp_radius
  have hrNumeric : (980859210269/1000000000000 : ℝ) ≤ Real.exp (-4433/229376 : ℝ) ∧ Real.exp (-4433/229376 : ℝ) ≤ (98085921027/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980859210269/1000000000000 : ℝ) ≤ (radius 7 (4433/32768 : ℝ)) ∧ (radius 7 (4433/32768 : ℝ)) ≤ (98085921027/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4433/32768 : ℝ)) (980859210269/1000000000000 : ℝ) (98085921027/100000000000 : ℝ) (194718282727/1000000000000 : ℝ) (194718282733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4433/32768 : ℝ)) (980859210269/1000000000000 : ℝ) (98085921027/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980859210269/1000000000000 : ℝ) (98085921027/100000000000 : ℝ) (495214802567/500000000000 : ℝ) (198085921027/200000000000 : ℝ) (990383365303/1000000000000 : ℝ) (123797920663/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 1 (495214802567/500000000000 : ℝ) (198085921027/200000000000 : ℝ) (990383365303/1000000000000 : ℝ) (123797920663/125000000000 : ℝ) (495203242609/500000000000 : ℝ) (49520324261/50000000000 : ℝ) (247601621237/250000000000 : ℝ) (19808129699/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 2 (495203242609/500000000000 : ℝ) (49520324261/50000000000 : ℝ) (247601621237/250000000000 : ℝ) (19808129699/20000000000 : ℝ) (990406485083/1000000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 3 (990406485083/1000000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 4 (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 5 (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 6 (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4433/32768 : ℝ)) 7 (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4433/32768 : ℝ))) (194718282727/1000000000000 : ℝ) (194718282733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194718282727/1000000000000 : ℝ) (194718282733/1000000000000 : ℝ) (597359141363/1000000000000 : ℝ) (597359141367/1000000000000 : ℝ) (220634473013/500000000000 : ℝ) (441268946033/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 1 (597359141363/1000000000000 : ℝ) (597359141367/1000000000000 : ℝ) (220634473013/500000000000 : ℝ) (441268946033/1000000000000 : ℝ) (259657021847/500000000000 : ℝ) (5193140437/10000000000 : ℝ) (256708024177/500000000000 : ℝ) (513416048361/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 2 (259657021847/500000000000 : ℝ) (5193140437/10000000000 : ℝ) (256708024177/500000000000 : ℝ) (513416048361/1000000000000 : ℝ) (64545630753/125000000000 : ℝ) (516365046031/1000000000000 : ℝ) (516356624987/1000000000000 : ℝ) (258178312497/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 3 (64545630753/125000000000 : ℝ) (516365046031/1000000000000 : ℝ) (516356624987/1000000000000 : ℝ) (258178312497/500000000000 : ℝ) (103272167101/200000000000 : ℝ) (516360835513/1000000000000 : ℝ) (16136276109/31250000000 : ℝ) (64545104437/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 4 (103272167101/200000000000 : ℝ) (516360835513/1000000000000 : ℝ) (16136276109/31250000000 : ℝ) (64545104437/125000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 5 (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 6 (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4433/32768 : ℝ))) 7 (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4433/32768 : ℝ)) hmem 8 (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4433/32768 : ℝ))) hcmem 8 (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4433/32768 : ℝ)) (495203242541/500000000000 : ℝ) (198081297017/200000000000 : ℝ) (64545104437/125000000000 : ℝ) (103272167101/200000000000 : ℝ) (51184647157/62500000000 : ℝ) (81895435453/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0255_exp_lower
  have heNumeric : (2019013794457/1000000000000 : ℝ)/4 ≤ Real.exp (-2187792606371/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013794457/1000000000000 : ℝ)/4 ≤ Real.exp ((8865/65536 : ℝ)-(81895435453/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8865/65536 : ℝ) (4433/32768 : ℝ) (81895435453/100000000000 : ℝ) (2019013794457/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0256; no trusted numerical premise.
theorem cover7_leaf0256_exp_radius : (997586850576698873/1000000000000000000 : ℝ) ≤ Real.exp ((-8867/458752 : ℝ)/8) ∧ Real.exp ((-8867/458752 : ℝ)/8) ≤ (498793425288349437/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8867/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0256_exp_lower : (918089262365481563/1000000000000000000 : ℝ) ≤ Real.exp ((-43755856587/64000000000 : ℝ)/8) ∧ Real.exp ((-43755856587/64000000000 : ℝ)/8) ≤ (229522315591370391/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43755856587/64000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0256_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901365377/100000000000 : ℝ) ≤ 4*Real.exp (4433/32768 : ℝ)*Real.exp (-mu (radius 7 (8867/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901365377/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8867/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0256_exp_radius
  have hrNumeric : (122607134021/125000000000 : ℝ) ≤ Real.exp (-8867/458752 : ℝ) ∧ Real.exp (-8867/458752 : ℝ) ≤ (980857072169/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122607134021/125000000000 : ℝ) ≤ (radius 7 (8867/65536 : ℝ)) ∧ (radius 7 (8867/65536 : ℝ)) ≤ (980857072169/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8867/65536 : ℝ)) (122607134021/125000000000 : ℝ) (980857072169/1000000000000 : ℝ) (194729052727/1000000000000 : ℝ) (194729052733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8867/65536 : ℝ)) (122607134021/125000000000 : ℝ) (980857072169/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122607134021/125000000000 : ℝ) (980857072169/1000000000000 : ℝ) (247607134021/250000000000 : ℝ) (198085707217/200000000000 : ℝ) (990382285871/1000000000000 : ℝ) (61898892867/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 1 (247607134021/250000000000 : ℝ) (198085707217/200000000000 : ℝ) (990382285871/1000000000000 : ℝ) (61898892867/62500000000 : ℝ) (990405410977/1000000000000 : ℝ) (990405410979/1000000000000 : ℝ) (990405410707/1000000000000 : ℝ) (990405410709/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 2 (990405410977/1000000000000 : ℝ) (990405410979/1000000000000 : ℝ) (990405410707/1000000000000 : ℝ) (990405410709/1000000000000 : ℝ) (495202705421/500000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 3 (495202705421/500000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 4 (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 5 (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 6 (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8867/65536 : ℝ)) 7 (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8867/65536 : ℝ))) (194729052727/1000000000000 : ℝ) (194729052733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194729052727/1000000000000 : ℝ) (194729052733/1000000000000 : ℝ) (597364526363/1000000000000 : ℝ) (597364526367/1000000000000 : ℝ) (441281149299/1000000000000 : ℝ) (441281149307/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 1 (597364526363/1000000000000 : ℝ) (597364526367/1000000000000 : ℝ) (441281149299/1000000000000 : ℝ) (441281149307/1000000000000 : ℝ) (519322837831/1000000000000 : ℝ) (519322837837/1000000000000 : ℝ) (513425461721/1000000000000 : ℝ) (16044545679/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 2 (519322837831/1000000000000 : ℝ) (519322837837/1000000000000 : ℝ) (513425461721/1000000000000 : ℝ) (16044545679/31250000000 : ℝ) (32273384361/62500000000 : ℝ) (516374149783/1000000000000 : ℝ) (103273146131/200000000000 : ℝ) (516365730663/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 3 (32273384361/62500000000 : ℝ) (516374149783/1000000000000 : ℝ) (103273146131/200000000000 : ℝ) (516365730663/1000000000000 : ℝ) (103273988043/200000000000 : ℝ) (516369940223/1000000000000 : ℝ) (258184970099/500000000000 : ℝ) (258184970103/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 4 (103273988043/200000000000 : ℝ) (516369940223/1000000000000 : ℝ) (258184970099/500000000000 : ℝ) (258184970103/500000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 5 (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 6 (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8867/65536 : ℝ))) 7 (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8867/65536 : ℝ)) hmem 8 (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8867/65536 : ℝ))) hcmem 8 (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8867/65536 : ℝ)) (990405410841/1000000000000 : ℝ) (247601352711/250000000000 : ℝ) (258184970103/500000000000 : ℝ) (103273988043/200000000000 : ℝ) (409484841491/500000000000 : ℝ) (818969683/1000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0256_exp_lower
  have heNumeric : (201901365377/100000000000 : ℝ)/4 ≤ Real.exp (-43755856587/64000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901365377/100000000000 : ℝ)/4 ≤ Real.exp ((4433/32768 : ℝ)-(818969683/1000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4433/32768 : ℝ) (8867/65536 : ℝ) (818969683/1000000000 : ℝ) (201901365377/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0257; no trusted numerical premise.
theorem cover7_leaf0257_exp_radius : (498793289377945413/500000000000000000 : ℝ) ≤ Real.exp ((-2217/114688 : ℝ)/8) ∧ Real.exp ((-2217/114688 : ℝ)/8) ≤ (997586578755890827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2217/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0257_exp_lower : (7344714036007253/8000000000000000 : ℝ) ≤ Real.exp ((-10938965243229/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938965243229/16000000000000 : ℝ)/8) ≤ (459044627250453313/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938965243229/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0257_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013515407/1000000000000 : ℝ) ≤ 4*Real.exp (8867/65536 : ℝ)*Real.exp (-mu (radius 7 (2217/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013515407/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2217/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0257_exp_radius
  have hrNumeric : (980854934071/1000000000000 : ℝ) ≤ Real.exp (-2217/114688 : ℝ) ∧ Real.exp (-2217/114688 : ℝ) ≤ (122606866759/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980854934071/1000000000000 : ℝ) ≤ (radius 7 (2217/16384 : ℝ)) ∧ (radius 7 (2217/16384 : ℝ)) ≤ (122606866759/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2217/16384 : ℝ)) (980854934071/1000000000000 : ℝ) (122606866759/125000000000 : ℝ) (194739822087/1000000000000 : ℝ) (194739822093/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2217/16384 : ℝ)) (980854934071/1000000000000 : ℝ) (122606866759/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980854934071/1000000000000 : ℝ) (122606866759/125000000000 : ℝ) (198085493407/200000000000 : ℝ) (247606866759/250000000000 : ℝ) (24759530161/25000000000 : ℝ) (495190603221/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 1 (198085493407/200000000000 : ℝ) (247606866759/250000000000 : ℝ) (24759530161/25000000000 : ℝ) (495190603221/500000000000 : ℝ) (990404336737/1000000000000 : ℝ) (990404336739/1000000000000 : ℝ) (990404336467/1000000000000 : ℝ) (990404336469/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 2 (990404336737/1000000000000 : ℝ) (990404336739/1000000000000 : ℝ) (990404336467/1000000000000 : ℝ) (990404336469/1000000000000 : ℝ) (495202168301/500000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 3 (495202168301/500000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 4 (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 5 (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 6 (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2217/16384 : ℝ)) 7 (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2217/16384 : ℝ))) (194739822087/1000000000000 : ℝ) (194739822093/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194739822087/1000000000000 : ℝ) (194739822093/1000000000000 : ℝ) (597369911043/1000000000000 : ℝ) (597369911047/1000000000000 : ℝ) (44129335151/100000000000 : ℝ) (441293351517/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 1 (597369911043/1000000000000 : ℝ) (597369911047/1000000000000 : ℝ) (44129335151/100000000000 : ℝ) (441293351517/1000000000000 : ℝ) (129832907819/250000000000 : ℝ) (259665815641/500000000000 : ℝ) (32089679643/62500000000 : ℝ) (102686974859/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 2 (129832907819/250000000000 : ℝ) (259665815641/500000000000 : ℝ) (32089679643/62500000000 : ℝ) (102686974859/200000000000 : ℝ) (258191626391/500000000000 : ℝ) (516383252789/1000000000000 : ℝ) (516374835577/1000000000000 : ℝ) (103274967117/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 3 (258191626391/500000000000 : ℝ) (516383252789/1000000000000 : ℝ) (516374835577/1000000000000 : ℝ) (103274967117/200000000000 : ℝ) (516379044179/1000000000000 : ℝ) (516379044187/1000000000000 : ℝ) (258189522081/500000000000 : ℝ) (51637904417/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 4 (516379044179/1000000000000 : ℝ) (516379044187/1000000000000 : ℝ) (258189522081/500000000000 : ℝ) (51637904417/100000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 5 (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 6 (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2217/16384 : ℝ))) 7 (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2217/16384 : ℝ)) hmem 8 (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2217/16384 : ℝ))) hcmem 8 (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2217/16384 : ℝ)) (990404336601/1000000000000 : ℝ) (247601084151/250000000000 : ℝ) (51637904417/100000000000 : ℝ) (516379044179/1000000000000 : ℝ) (818985010301/1000000000000 : ℝ) (818985010319/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0257_exp_lower
  have heNumeric : (2019013515407/1000000000000 : ℝ)/4 ≤ Real.exp (-10938965243229/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013515407/1000000000000 : ℝ)/4 ≤ Real.exp ((8867/65536 : ℝ)-(818985010319/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8867/65536 : ℝ) (2217/16384 : ℝ) (818985010319/1000000000000 : ℝ) (2019013515407/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0258; no trusted numerical premise.
theorem cover7_leaf0258_exp_radius : (249396576733789211/250000000000000000 : ℝ) ≤ Real.exp ((-1267/65536 : ℝ)/8) ∧ Real.exp ((-1267/65536 : ℝ)/8) ≤ (199517261387031369/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1267/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0258_exp_lower : (918089246770143263/1000000000000000000 : ℝ) ≤ Real.exp ((-2734741580263/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734741580263/4000000000000 : ℝ)/8) ≤ (28690288961566977/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734741580263/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0258_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506689699/500000000000 : ℝ) ≤ 4*Real.exp (2217/16384 : ℝ)*Real.exp (-mu (radius 7 (8869/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506689699/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8869/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0258_exp_radius
  have hrNumeric : (49042639799/50000000000 : ℝ) ≤ Real.exp (-1267/65536 : ℝ) ∧ Real.exp (-1267/65536 : ℝ) ≤ (980852795981/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49042639799/50000000000 : ℝ) ≤ (radius 7 (8869/65536 : ℝ)) ∧ (radius 7 (8869/65536 : ℝ)) ≤ (980852795981/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8869/65536 : ℝ)) (49042639799/50000000000 : ℝ) (980852795981/1000000000000 : ℝ) (97375295399/500000000000 : ℝ) (48687647701/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8869/65536 : ℝ)) (49042639799/50000000000 : ℝ) (980852795981/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49042639799/50000000000 : ℝ) (980852795981/1000000000000 : ℝ) (99042639799/100000000000 : ℝ) (990426397991/1000000000000 : ℝ) (990380127011/1000000000000 : ℝ) (990380127013/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 1 (99042639799/100000000000 : ℝ) (990426397991/1000000000000 : ℝ) (990380127011/1000000000000 : ℝ) (990380127013/1000000000000 : ℝ) (79232261/80000000 : ℝ) (495201631251/500000000000 : ℝ) (99040326223/100000000000 : ℝ) (123800407779/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 2 (79232261/80000000 : ℝ) (495201631251/500000000000 : ℝ) (99040326223/100000000000 : ℝ) (123800407779/125000000000 : ℝ) (198080652473/200000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 3 (198080652473/200000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 4 (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 5 (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 6 (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8869/65536 : ℝ)) 7 (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8869/65536 : ℝ))) (97375295399/500000000000 : ℝ) (48687647701/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97375295399/500000000000 : ℝ) (48687647701/250000000000 : ℝ) (597375295399/1000000000000 : ℝ) (298687647701/500000000000 : ℝ) (55163194081/125000000000 : ℝ) (88261110531/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 1 (597375295399/1000000000000 : ℝ) (298687647701/500000000000 : ℝ) (55163194081/125000000000 : ℝ) (88261110531/200000000000 : ℝ) (519340424023/1000000000000 : ℝ) (519340424029/1000000000000 : ℝ) (513444286047/1000000000000 : ℝ) (513444286053/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 2 (519340424023/1000000000000 : ℝ) (519340424029/1000000000000 : ℝ) (513444286047/1000000000000 : ℝ) (513444286053/1000000000000 : ℝ) (103278471007/200000000000 : ℝ) (516392355041/1000000000000 : ℝ) (258191969873/500000000000 : ℝ) (516383939753/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 3 (103278471007/200000000000 : ℝ) (516392355041/1000000000000 : ℝ) (258191969873/500000000000 : ℝ) (516383939753/1000000000000 : ℝ) (51638814739/100000000000 : ℝ) (516388147397/1000000000000 : ℝ) (516388147373/1000000000000 : ℝ) (25819407369/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 4 (51638814739/100000000000 : ℝ) (516388147397/1000000000000 : ℝ) (516388147373/1000000000000 : ℝ) (25819407369/50000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 5 (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 6 (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8869/65536 : ℝ))) 7 (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8869/65536 : ℝ)) hmem 8 (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8869/65536 : ℝ))) hcmem 8 (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8869/65536 : ℝ)) (247600815591/250000000000 : ℝ) (990403262367/1000000000000 : ℝ) (516388147381/1000000000000 : ℝ) (516388147389/1000000000000 : ℝ) (102375042057/125000000000 : ℝ) (102375042059/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0258_exp_lower
  have heNumeric : (1009506689699/500000000000 : ℝ)/4 ≤ Real.exp (-2734741580263/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506689699/500000000000 : ℝ)/4 ≤ Real.exp ((2217/16384 : ℝ)-(102375042059/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2217/16384 : ℝ) (8869/65536 : ℝ) (102375042059/125000000000 : ℝ) (1009506689699/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0259; no trusted numerical premise.
theorem cover7_leaf0259_exp_radius : (31174563597328029/31250000000000000 : ℝ) ≤ Real.exp ((-4435/229376 : ℝ)/8) ∧ Real.exp ((-4435/229376 : ℝ)/8) ≤ (997586035114496929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4435/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0259_exp_lower : (918089239171125771/1000000000000000000 : ℝ) ≤ Real.exp ((-10938967380507/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938967380507/16000000000000 : ℝ)/8) ≤ (229522309792781443/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938967380507/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0259_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753311427/250000000000 : ℝ) ≤ 4*Real.exp (8869/65536 : ℝ)*Real.exp (-mu (radius 7 (4435/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504753311427/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4435/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0259_exp_radius
  have hrNumeric : (980850657893/1000000000000 : ℝ) ≤ Real.exp (-4435/229376 : ℝ) ∧ Real.exp (-4435/229376 : ℝ) ≤ (490425328947/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980850657893/1000000000000 : ℝ) ≤ (radius 7 (4435/32768 : ℝ)) ∧ (radius 7 (4435/32768 : ℝ)) ≤ (490425328947/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4435/32768 : ℝ)) (980850657893/1000000000000 : ℝ) (490425328947/500000000000 : ℝ) (19476135887/100000000000 : ℝ) (48690339719/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4435/32768 : ℝ)) (980850657893/1000000000000 : ℝ) (490425328947/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980850657893/1000000000000 : ℝ) (490425328947/500000000000 : ℝ) (495212664473/500000000000 : ℝ) (990425328947/1000000000000 : ℝ) (990379047583/1000000000000 : ℝ) (198075809517/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 1 (495212664473/500000000000 : ℝ) (990425328947/1000000000000 : ℝ) (990379047583/1000000000000 : ℝ) (198075809517/200000000000 : ℝ) (123800273533/125000000000 : ℝ) (495201094133/500000000000 : ℝ) (495201093997/500000000000 : ℝ) (247600546999/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 2 (123800273533/125000000000 : ℝ) (495201094133/500000000000 : ℝ) (495201093997/500000000000 : ℝ) (247600546999/250000000000 : ℝ) (990402188129/1000000000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 3 (990402188129/1000000000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 4 (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 5 (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 6 (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4435/32768 : ℝ)) 7 (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4435/32768 : ℝ))) (19476135887/100000000000 : ℝ) (48690339719/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19476135887/100000000000 : ℝ) (48690339719/250000000000 : ℝ) (119476135887/200000000000 : ℝ) (298690339719/500000000000 : ℝ) (110329438181/250000000000 : ℝ) (110329438183/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 1 (119476135887/200000000000 : ℝ) (298690339719/500000000000 : ℝ) (110329438181/250000000000 : ℝ) (110329438183/250000000000 : ℝ) (519349216079/1000000000000 : ℝ) (103869843217/200000000000 : ℝ) (102690739401/200000000000 : ℝ) (128363424253/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 2 (519349216079/1000000000000 : ℝ) (103869843217/200000000000 : ℝ) (102690739401/200000000000 : ℝ) (128363424253/250000000000 : ℝ) (258200728271/500000000000 : ℝ) (516401456549/1000000000000 : ℝ) (16137282599/31250000000 : ℝ) (20655721727/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 3 (258200728271/500000000000 : ℝ) (516401456549/1000000000000 : ℝ) (16137282599/31250000000 : ℝ) (20655721727/40000000000 : ℝ) (103279449971/200000000000 : ℝ) (258198624931/500000000000 : ℝ) (516397249837/1000000000000 : ℝ) (103279449969/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 4 (103279449971/200000000000 : ℝ) (258198624931/500000000000 : ℝ) (516397249837/1000000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624923/500000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 5 (258198624923/500000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 6 (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4435/32768 : ℝ))) 7 (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4435/32768 : ℝ)) hmem 8 (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4435/32768 : ℝ))) hcmem 8 (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4435/32768 : ℝ)) (30950068379/31250000000 : ℝ) (990402188131/1000000000000 : ℝ) (103279449969/200000000000 : ℝ) (258198624927/500000000000 : ℝ) (819015661459/1000000000000 : ℝ) (819015661477/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0259_exp_lower
  have heNumeric : (504753311427/250000000000 : ℝ)/4 ≤ Real.exp (-10938967380507/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753311427/250000000000 : ℝ)/4 ≤ Real.exp ((8869/65536 : ℝ)-(819015661477/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8869/65536 : ℝ) (4435/32768 : ℝ) (819015661477/1000000000000 : ℝ) (504753311427/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0260; no trusted numerical premise.
theorem cover7_leaf0260_exp_radius : (249396440823477769/250000000000000000 : ℝ) ≤ Real.exp ((-8871/458752 : ℝ)/8) ∧ Real.exp ((-8871/458752 : ℝ)/8) ≤ (997585763293911077/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8871/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0260_exp_lower : (114761153963039149/125000000000000000 : ℝ) ≤ Real.exp ((-1093896842153/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093896842153/1600000000000 : ℝ)/8) ≤ (918089231704313193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093896842153/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0260_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013114343/1000000000000 : ℝ) ≤ 4*Real.exp (4435/32768 : ℝ)*Real.exp (-mu (radius 7 (8871/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013114343/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8871/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0260_exp_radius
  have hrNumeric : (98084851981/100000000000 : ℝ) ≤ Real.exp (-8871/458752 : ℝ) ∧ Real.exp (-8871/458752 : ℝ) ≤ (980848519811/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98084851981/100000000000 : ℝ) ≤ (radius 7 (8871/65536 : ℝ)) ∧ (radius 7 (8871/65536 : ℝ)) ≤ (980848519811/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8871/65536 : ℝ)) (98084851981/100000000000 : ℝ) (980848519811/1000000000000 : ℝ) (97386063151/500000000000 : ℝ) (48693031577/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8871/65536 : ℝ)) (98084851981/100000000000 : ℝ) (980848519811/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98084851981/100000000000 : ℝ) (980848519811/1000000000000 : ℝ) (198084851981/200000000000 : ℝ) (495212129953/500000000000 : ℝ) (247594492039/250000000000 : ℝ) (495188984079/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 1 (198084851981/200000000000 : ℝ) (495212129953/500000000000 : ℝ) (247594492039/250000000000 : ℝ) (495188984079/500000000000 : ℝ) (99040111403/100000000000 : ℝ) (61900069627/62500000000 : ℝ) (6190006961/6250000000 : ℝ) (495200556881/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 2 (99040111403/100000000000 : ℝ) (61900069627/62500000000 : ℝ) (6190006961/6250000000 : ℝ) (495200556881/500000000000 : ℝ) (198080222779/200000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 3 (198080222779/200000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 4 (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 5 (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 6 (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8871/65536 : ℝ)) 7 (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8871/65536 : ℝ))) (97386063151/500000000000 : ℝ) (48693031577/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97386063151/500000000000 : ℝ) (48693031577/250000000000 : ℝ) (597386063151/1000000000000 : ℝ) (298693031577/500000000000 : ℝ) (441329951739/1000000000000 : ℝ) (220664975873/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 1 (597386063151/1000000000000 : ℝ) (298693031577/500000000000 : ℝ) (441329951739/1000000000000 : ℝ) (220664975873/500000000000 : ℝ) (103871601489/200000000000 : ℝ) (10387160149/20000000000 : ℝ) (102692621433/200000000000 : ℝ) (513463107171/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 2 (103871601489/200000000000 : ℝ) (10387160149/20000000000 : ℝ) (102692621433/200000000000 : ℝ) (513463107171/1000000000000 : ℝ) (103282111461/200000000000 : ℝ) (516410557311/1000000000000 : ℝ) (103280429169/200000000000 : ℝ) (516402145851/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 3 (103282111461/200000000000 : ℝ) (516410557311/1000000000000 : ℝ) (103280429169/200000000000 : ℝ) (516402145851/1000000000000 : ℝ) (20656254063/40000000000 : ℝ) (516406351581/1000000000000 : ℝ) (516406351557/1000000000000 : ℝ) (129101587891/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 4 (20656254063/40000000000 : ℝ) (516406351581/1000000000000 : ℝ) (516406351557/1000000000000 : ℝ) (129101587891/250000000000 : ℝ) (258203175783/500000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 5 (258203175783/500000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 6 (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8871/65536 : ℝ))) 7 (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8871/65536 : ℝ)) hmem 8 (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8871/65536 : ℝ))) hcmem 8 (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8871/65536 : ℝ)) (495200556947/500000000000 : ℝ) (990401113897/1000000000000 : ℝ) (103281270313/200000000000 : ℝ) (516406351573/1000000000000 : ℝ) (409515492657/500000000000 : ℝ) (81903098533/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0260_exp_lower
  have heNumeric : (2019013114343/1000000000000 : ℝ)/4 ≤ Real.exp (-1093896842153/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013114343/1000000000000 : ℝ)/4 ≤ Real.exp ((4435/32768 : ℝ)-(81903098533/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4435/32768 : ℝ) (8871/65536 : ℝ) (81903098533/100000000000 : ℝ) (2019013114343/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0261; no trusted numerical premise.
theorem cover7_leaf0261_exp_radius : (99758549147339929/100000000000000000 : ℝ) ≤ Real.exp ((-1109/57344 : ℝ)/8) ∧ Real.exp ((-1109/57344 : ℝ)/8) ≤ (997585491473399291/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1109/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0261_exp_lower : (918089224369590761/1000000000000000000 : ℝ) ≤ Real.exp ((-10938969444137/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938969444137/16000000000000 : ℝ)/8) ≤ (459044612184795381/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938969444137/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0261_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506492651/500000000000 : ℝ) ≤ 4*Real.exp (8871/65536 : ℝ)*Real.exp (-mu (radius 7 (1109/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506492651/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1109/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0261_exp_radius
  have hrNumeric : (245211595433/250000000000 : ℝ) ≤ Real.exp (-1109/57344 : ℝ) ∧ Real.exp (-1109/57344 : ℝ) ≤ (980846381733/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245211595433/250000000000 : ℝ) ≤ (radius 7 (1109/8192 : ℝ)) ∧ (radius 7 (1109/8192 : ℝ)) ≤ (980846381733/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1109/8192 : ℝ)) (245211595433/250000000000 : ℝ) (980846381733/1000000000000 : ℝ) (194782893091/1000000000000 : ℝ) (97391446549/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1109/8192 : ℝ)) (245211595433/250000000000 : ℝ) (980846381733/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245211595433/250000000000 : ℝ) (980846381733/1000000000000 : ℝ) (495211595433/500000000000 : ℝ) (990423190867/1000000000000 : ℝ) (99037688873/100000000000 : ℝ) (247594222183/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 1 (495211595433/500000000000 : ℝ) (990423190867/1000000000000 : ℝ) (99037688873/100000000000 : ℝ) (247594222183/250000000000 : ℝ) (495200019899/500000000000 : ℝ) (4952000199/5000000000 : ℝ) (990400039527/1000000000000 : ℝ) (990400039529/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 2 (495200019899/500000000000 : ℝ) (4952000199/5000000000 : ℝ) (990400039527/1000000000000 : ℝ) (990400039529/1000000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 3 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 4 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 5 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 6 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1109/8192 : ℝ)) 7 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1109/8192 : ℝ))) (194782893091/1000000000000 : ℝ) (97391446549/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194782893091/1000000000000 : ℝ) (97391446549/500000000000 : ℝ) (119478289309/200000000000 : ℝ) (597391446549/1000000000000 : ℝ) (441342149687/1000000000000 : ℝ) (6895971089/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 1 (119478289309/200000000000 : ℝ) (597391446549/1000000000000 : ℝ) (441342149687/1000000000000 : ℝ) (6895971089/15625000000 : ℝ) (129841699529/250000000000 : ℝ) (519366798123/1000000000000 : ℝ) (513472516521/1000000000000 : ℝ) (513472516529/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 2 (129841699529/250000000000 : ℝ) (519366798123/1000000000000 : ℝ) (513472516521/1000000000000 : ℝ) (513472516529/1000000000000 : ℝ) (258209828659/500000000000 : ℝ) (258209828663/500000000000 : ℝ) (129102811943/250000000000 : ℝ) (516411247781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 3 (258209828659/500000000000 : ℝ) (258209828663/500000000000 : ℝ) (129102811943/250000000000 : ℝ) (516411247781/1000000000000 : ℝ) (103283090509/200000000000 : ℝ) (258207726277/500000000000 : ℝ) (516415452527/1000000000000 : ℝ) (516415452537/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 4 (103283090509/200000000000 : ℝ) (258207726277/500000000000 : ℝ) (516415452527/1000000000000 : ℝ) (516415452537/1000000000000 : ℝ) (64551931567/125000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 5 (64551931567/125000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 6 (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1109/8192 : ℝ))) 7 (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1109/8192 : ℝ)) hmem 8 (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1109/8192 : ℝ))) hcmem 8 (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1109/8192 : ℝ)) (495200019831/500000000000 : ℝ) (198080007933/200000000000 : ℝ) (103283090507/200000000000 : ℝ) (258207726273/500000000000 : ℝ) (819046308011/1000000000000 : ℝ) (12797598563/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0261_exp_lower
  have heNumeric : (1009506492651/500000000000 : ℝ)/4 ≤ Real.exp (-10938969444137/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506492651/500000000000 : ℝ)/4 ≤ Real.exp ((8871/65536 : ℝ)-(12797598563/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8871/65536 : ℝ) (1109/8192 : ℝ) (12797598563/15625000000 : ℝ) (1009506492651/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0262; no trusted numerical premise.
theorem cover7_leaf0262_exp_radius : (997585219652961569/1000000000000000000 : ℝ) ≤ Real.exp ((-8873/458752 : ℝ)/8) ∧ Real.exp ((-8873/458752 : ℝ)/8) ≤ (99758521965296157/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8873/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0262_exp_lower : (183617843433621217/200000000000000000 : ℝ) ≤ Real.exp ((-1367371306021/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367371306021/2000000000000 : ℝ)/8) ≤ (459044608584053043/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367371306021/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0262_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802571721/200000000000 : ℝ) ≤ 4*Real.exp (1109/8192 : ℝ)*Real.exp (-mu (radius 7 (8873/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403802571721/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8873/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0262_exp_radius
  have hrNumeric : (980844243659/1000000000000 : ℝ) ≤ Real.exp (-8873/458752 : ℝ) ∧ Real.exp (-8873/458752 : ℝ) ≤ (49042212183/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980844243659/1000000000000 : ℝ) ≤ (radius 7 (8873/65536 : ℝ)) ∧ (radius 7 (8873/65536 : ℝ)) ≤ (49042212183/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8873/65536 : ℝ)) (980844243659/1000000000000 : ℝ) (49042212183/50000000000 : ℝ) (194793659237/1000000000000 : ℝ) (194793659243/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8873/65536 : ℝ)) (980844243659/1000000000000 : ℝ) (49042212183/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980844243659/1000000000000 : ℝ) (49042212183/50000000000 : ℝ) (990422121829/1000000000000 : ℝ) (99042212183/100000000000 : ℝ) (495187904653/500000000000 : ℝ) (990375809307/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 1 (990422121829/1000000000000 : ℝ) (99042212183/100000000000 : ℝ) (495187904653/500000000000 : ℝ) (990375809307/1000000000000 : ℝ) (990398965567/1000000000000 : ℝ) (990398965569/1000000000000 : ℝ) (61899935331/62500000000 : ℝ) (495199482649/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 2 (990398965567/1000000000000 : ℝ) (990398965569/1000000000000 : ℝ) (61899935331/62500000000 : ℝ) (495199482649/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 3 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 4 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 5 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 6 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8873/65536 : ℝ)) 7 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8873/65536 : ℝ))) (194793659237/1000000000000 : ℝ) (194793659243/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194793659237/1000000000000 : ℝ) (194793659243/1000000000000 : ℝ) (298698414809/500000000000 : ℝ) (298698414811/500000000000 : ℝ) (44135434657/100000000000 : ℝ) (220677173289/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 1 (298698414809/500000000000 : ℝ) (298698414811/500000000000 : ℝ) (44135434657/100000000000 : ℝ) (220677173289/500000000000 : ℝ) (259687794047/500000000000 : ℝ) (5193755881/10000000000 : ℝ) (20539277003/40000000000 : ℝ) (256740962541/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 2 (259687794047/500000000000 : ℝ) (5193755881/10000000000 : ℝ) (20539277003/40000000000 : ℝ) (256740962541/500000000000 : ℝ) (64553594573/125000000000 : ℝ) (516428756591/1000000000000 : ℝ) (516420348951/1000000000000 : ℝ) (516420348959/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 3 (64553594573/125000000000 : ℝ) (516428756591/1000000000000 : ℝ) (516420348951/1000000000000 : ℝ) (516420348959/1000000000000 : ℝ) (516424552767/1000000000000 : ℝ) (20656982111/40000000000 : ℝ) (2065698211/4000000000 : ℝ) (258212276379/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 4 (516424552767/1000000000000 : ℝ) (20656982111/40000000000 : ℝ) (2065698211/4000000000 : ℝ) (258212276379/500000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 5 (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 6 (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8873/65536 : ℝ))) 7 (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8873/65536 : ℝ)) hmem 8 (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8873/65536 : ℝ))) hcmem 8 (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8873/65536 : ℝ)) (990398965431/1000000000000 : ℝ) (495199482717/500000000000 : ℝ) (258212276379/500000000000 : ℝ) (516424552767/1000000000000 : ℝ) (204765407389/250000000000 : ℝ) (819061629573/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0262_exp_lower
  have heNumeric : (403802571721/200000000000 : ℝ)/4 ≤ Real.exp (-1367371306021/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802571721/200000000000 : ℝ)/4 ≤ Real.exp ((1109/8192 : ℝ)-(819061629573/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1109/8192 : ℝ) (8873/65536 : ℝ) (819061629573/1000000000000 : ℝ) (403802571721/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0263; no trusted numerical premise.
theorem cover7_leaf0263_exp_radius : (997584947832597913/1000000000000000000 : ℝ) ≤ Real.exp ((-4437/229376 : ℝ)/8) ∧ Real.exp ((-4437/229376 : ℝ)/8) ≤ (498792473916298957/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4437/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0263_exp_lower : (918089210099170597/1000000000000000000 : ℝ) ≤ Real.exp ((-10938971433719/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938971433719/16000000000000 : ℝ)/8) ≤ (459044605049585299/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938971433719/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0263_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (12618829589/6250000000 : ℝ) ≤ 4*Real.exp (8873/65536 : ℝ)*Real.exp (-mu (radius 7 (4437/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (12618829589/6250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4437/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0263_exp_radius
  have hrNumeric : (980842105591/1000000000000 : ℝ) ≤ Real.exp (-4437/229376 : ℝ) ∧ Real.exp (-4437/229376 : ℝ) ≤ (122605263199/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980842105591/1000000000000 : ℝ) ≤ (radius 7 (4437/32768 : ℝ)) ∧ (radius 7 (4437/32768 : ℝ)) ≤ (122605263199/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4437/32768 : ℝ)) (980842105591/1000000000000 : ℝ) (122605263199/125000000000 : ℝ) (97402212369/500000000000 : ℝ) (24350553093/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4437/32768 : ℝ)) (980842105591/1000000000000 : ℝ) (122605263199/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980842105591/1000000000000 : ℝ) (122605263199/125000000000 : ℝ) (198084210559/200000000000 : ℝ) (247605263199/250000000000 : ℝ) (990374729883/1000000000000 : ℝ) (247593682471/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 1 (198084210559/200000000000 : ℝ) (247605263199/250000000000 : ℝ) (990374729883/1000000000000 : ℝ) (247593682471/250000000000 : ℝ) (990397891339/1000000000000 : ℝ) (49519894567/50000000000 : ℝ) (247599472767/250000000000 : ℝ) (99039789107/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 2 (990397891339/1000000000000 : ℝ) (49519894567/50000000000 : ℝ) (247599472767/250000000000 : ℝ) (99039789107/100000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 3 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 4 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 5 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 6 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4437/32768 : ℝ)) 7 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4437/32768 : ℝ))) (97402212369/500000000000 : ℝ) (24350553093/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97402212369/500000000000 : ℝ) (24350553093/125000000000 : ℝ) (597402212369/1000000000000 : ℝ) (149350553093/250000000000 : ℝ) (220683271193/500000000000 : ℝ) (220683271197/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 1 (597402212369/1000000000000 : ℝ) (149350553093/250000000000 : ℝ) (220683271193/500000000000 : ℝ) (220683271197/500000000000 : ℝ) (519384377377/1000000000000 : ℝ) (519384377383/1000000000000 : ℝ) (20539653313/40000000000 : ℝ) (16046604151/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 2 (519384377377/1000000000000 : ℝ) (519384377383/1000000000000 : ℝ) (20539653313/40000000000 : ℝ) (16046604151/31250000000 : ℝ) (516437855101/1000000000000 : ℝ) (129109463777/250000000000 : ℝ) (25821472469/50000000000 : ℝ) (129107362347/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 3 (516437855101/1000000000000 : ℝ) (129109463777/250000000000 : ℝ) (25821472469/50000000000 : ℝ) (129107362347/250000000000 : ℝ) (6455420653/12500000000 : ℝ) (64554206531/125000000000 : ℝ) (516433652223/1000000000000 : ℝ) (516433652231/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 4 (6455420653/12500000000 : ℝ) (64554206531/125000000000 : ℝ) (516433652223/1000000000000 : ℝ) (516433652231/1000000000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 5 (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 6 (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4437/32768 : ℝ))) 7 (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4437/32768 : ℝ)) hmem 8 (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4437/32768 : ℝ))) hcmem 8 (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4437/32768 : ℝ)) (990397891203/1000000000000 : ℝ) (198079578241/200000000000 : ℝ) (516433652231/1000000000000 : ℝ) (6455420653/12500000000 : ℝ) (409538474971/500000000000 : ℝ) (819076949959/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0263_exp_lower
  have heNumeric : (12618829589/6250000000 : ℝ)/4 ≤ Real.exp (-10938971433719/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (12618829589/6250000000 : ℝ)/4 ≤ Real.exp ((8873/65536 : ℝ)-(819076949959/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8873/65536 : ℝ) (4437/32768 : ℝ) (819076949959/1000000000000 : ℝ) (12618829589/6250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0264; no trusted numerical premise.
theorem cover7_leaf0264_exp_radius : (498792338006154161/500000000000000000 : ℝ) ≤ Real.exp ((-8875/458752 : ℝ)/8) ∧ Real.exp ((-8875/458752 : ℝ)/8) ≤ (997584676012308323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8875/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0264_exp_lower : (918089203161866201/1000000000000000000 : ℝ) ≤ Real.exp ((-5469486200459/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469486200459/8000000000000 : ℝ)/8) ≤ (459044601580933101/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469486200459/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0264_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901261219/100000000000 : ℝ) ≤ 4*Real.exp (4437/32768 : ℝ)*Real.exp (-mu (radius 7 (8875/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901261219/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8875/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0264_exp_radius
  have hrNumeric : (980839967527/1000000000000 : ℝ) ≤ Real.exp (-8875/458752 : ℝ) ∧ Real.exp (-8875/458752 : ℝ) ≤ (122604995941/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980839967527/1000000000000 : ℝ) ≤ (radius 7 (8875/65536 : ℝ)) ∧ (radius 7 (8875/65536 : ℝ)) ≤ (122604995941/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8875/65536 : ℝ)) (980839967527/1000000000000 : ℝ) (122604995941/125000000000 : ℝ) (97407594801/500000000000 : ℝ) (24351898701/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8875/65536 : ℝ)) (980839967527/1000000000000 : ℝ) (122604995941/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980839967527/1000000000000 : ℝ) (122604995941/125000000000 : ℝ) (990419983763/1000000000000 : ℝ) (247604995941/250000000000 : ℝ) (49518682523/50000000000 : ℝ) (495186825231/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 1 (990419983763/1000000000000 : ℝ) (247604995941/250000000000 : ℝ) (49518682523/50000000000 : ℝ) (495186825231/500000000000 : ℝ) (990396817111/1000000000000 : ℝ) (990396817113/1000000000000 : ℝ) (24759920421/25000000000 : ℝ) (990396816843/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 2 (990396817111/1000000000000 : ℝ) (990396817113/1000000000000 : ℝ) (24759920421/25000000000 : ℝ) (990396816843/1000000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 3 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 4 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 5 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 6 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8875/65536 : ℝ)) 7 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8875/65536 : ℝ))) (97407594801/500000000000 : ℝ) (24351898701/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97407594801/500000000000 : ℝ) (24351898701/125000000000 : ℝ) (597407594801/1000000000000 : ℝ) (149351898701/250000000000 : ℝ) (441378737143/1000000000000 : ℝ) (8827574743/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 1 (597407594801/1000000000000 : ℝ) (149351898701/250000000000 : ℝ) (441378737143/1000000000000 : ℝ) (8827574743/20000000000 : ℝ) (129848291493/250000000000 : ℝ) (519393165977/1000000000000 : ℝ) (256750369889/500000000000 : ℝ) (64187592473/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 2 (129848291493/250000000000 : ℝ) (519393165977/1000000000000 : ℝ) (256750369889/500000000000 : ℝ) (64187592473/125000000000 : ℝ) (4131575623/8000000000 : ℝ) (516446952881/1000000000000 : ℝ) (258219274533/500000000000 : ℝ) (516438549073/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 3 (4131575623/8000000000 : ℝ) (516446952881/1000000000000 : ℝ) (258219274533/500000000000 : ℝ) (516438549073/1000000000000 : ℝ) (51644275097/100000000000 : ℝ) (516442750977/1000000000000 : ℝ) (516442750953/1000000000000 : ℝ) (6455534387/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 4 (51644275097/100000000000 : ℝ) (516442750977/1000000000000 : ℝ) (516442750953/1000000000000 : ℝ) (6455534387/12500000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 5 (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 6 (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8875/65536 : ℝ))) 7 (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8875/65536 : ℝ)) hmem 8 (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8875/65536 : ℝ))) hcmem 8 (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8875/65536 : ℝ)) (39615872679/40000000000 : ℝ) (495198408489/500000000000 : ℝ) (516442750961/1000000000000 : ℝ) (516442750969/1000000000000 : ℝ) (409546134591/500000000000 : ℝ) (409546134599/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0264_exp_lower
  have heNumeric : (201901261219/100000000000 : ℝ)/4 ≤ Real.exp (-5469486200459/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901261219/100000000000 : ℝ)/4 ≤ Real.exp ((4437/32768 : ℝ)-(409546134599/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4437/32768 : ℝ) (8875/65536 : ℝ) (409546134599/500000000000 : ℝ) (201901261219/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0265; no trusted numerical premise.
theorem cover7_leaf0265_exp_radius : (997584404192092797/1000000000000000000 : ℝ) ≤ Real.exp ((-317/16384 : ℝ)/8) ∧ Real.exp ((-317/16384 : ℝ)/8) ≤ (498792202096046399/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-317/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0265_exp_lower : (918089196357340509/1000000000000000000 : ℝ) ≤ Real.exp ((-2187794669921/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187794669921/3200000000000 : ℝ)/8) ≤ (91808919635734051/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187794669921/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0265_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012492477/1000000000000 : ℝ) ≤ 4*Real.exp (8875/65536 : ℝ)*Real.exp (-mu (radius 7 (2219/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012492477/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2219/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0265_exp_radius
  have hrNumeric : (245209457367/250000000000 : ℝ) ≤ Real.exp (-317/16384 : ℝ) ∧ Real.exp (-317/16384 : ℝ) ≤ (980837829469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245209457367/250000000000 : ℝ) ≤ (radius 7 (2219/16384 : ℝ)) ∧ (radius 7 (2219/16384 : ℝ)) ≤ (980837829469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2219/16384 : ℝ)) (245209457367/250000000000 : ℝ) (980837829469/1000000000000 : ℝ) (194825953821/1000000000000 : ℝ) (194825953827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2219/16384 : ℝ)) (245209457367/250000000000 : ℝ) (980837829469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245209457367/250000000000 : ℝ) (980837829469/1000000000000 : ℝ) (495209457367/500000000000 : ℝ) (198083782947/200000000000 : ℝ) (990372571039/1000000000000 : ℝ) (990372571041/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 1 (495209457367/500000000000 : ℝ) (198083782947/200000000000 : ℝ) (990372571039/1000000000000 : ℝ) (990372571041/1000000000000 : ℝ) (495197871443/500000000000 : ℝ) (123799467861/125000000000 : ℝ) (198079148523/200000000000 : ℝ) (990395742617/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 2 (495197871443/500000000000 : ℝ) (123799467861/125000000000 : ℝ) (198079148523/200000000000 : ℝ) (990395742617/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 3 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 4 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 5 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 6 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2219/16384 : ℝ)) 7 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2219/16384 : ℝ))) (194825953821/1000000000000 : ℝ) (194825953827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194825953821/1000000000000 : ℝ) (194825953827/1000000000000 : ℝ) (59741297691/100000000000 : ℝ) (298706488457/500000000000 : ℝ) (27586933177/62500000000 : ℝ) (11034773271/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 1 (59741297691/100000000000 : ℝ) (298706488457/500000000000 : ℝ) (27586933177/62500000000 : ℝ) (11034773271/25000000000 : ℝ) (519401953871/1000000000000 : ℝ) (519401953877/1000000000000 : ℝ) (256755072963/500000000000 : ℝ) (513510145933/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 2 (519401953871/1000000000000 : ℝ) (519401953877/1000000000000 : ℝ) (256755072963/500000000000 : ℝ) (513510145933/1000000000000 : ℝ) (258228024949/500000000000 : ℝ) (103291209981/200000000000 : ℝ) (516447648001/1000000000000 : ℝ) (516447648009/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 3 (258228024949/500000000000 : ℝ) (103291209981/200000000000 : ℝ) (516447648001/1000000000000 : ℝ) (516447648009/1000000000000 : ℝ) (516451848949/1000000000000 : ℝ) (516451848957/1000000000000 : ℝ) (129112962233/250000000000 : ℝ) (25822592447/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 4 (516451848949/1000000000000 : ℝ) (516451848957/1000000000000 : ℝ) (129112962233/250000000000 : ℝ) (25822592447/50000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 5 (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 6 (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2219/16384 : ℝ))) 7 (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2219/16384 : ℝ)) hmem 8 (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2219/16384 : ℝ))) hcmem 8 (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2219/16384 : ℝ)) (3961582971/4000000000 : ℝ) (990395742753/1000000000000 : ℝ) (25822592447/50000000000 : ℝ) (516451848949/1000000000000 : ℝ) (409553793631/500000000000 : ℝ) (10238844841/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0265_exp_lower
  have heNumeric : (2019012492477/1000000000000 : ℝ)/4 ≤ Real.exp (-2187794669921/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012492477/1000000000000 : ℝ)/4 ≤ Real.exp ((8875/65536 : ℝ)-(10238844841/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8875/65536 : ℝ) (2219/16384 : ℝ) (10238844841/12500000000 : ℝ) (2019012492477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0266; no trusted numerical premise.
theorem cover7_leaf0266_exp_radius : (124698016546493917/125000000000000000 : ℝ) ≤ Real.exp ((-8877/458752 : ℝ)/8) ∧ Real.exp ((-8877/458752 : ℝ)/8) ≤ (997584132371951337/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8877/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0266_exp_lower : (57380574355328077/62500000000000000 : ℝ) ≤ Real.exp ((-2734743569957/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734743569957/4000000000000 : ℝ)/8) ≤ (918089189685249233/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734743569957/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0266_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506187547/500000000000 : ℝ) ≤ 4*Real.exp (2219/16384 : ℝ)*Real.exp (-mu (radius 7 (8877/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506187547/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8877/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0266_exp_radius
  have hrNumeric : (490417845707/500000000000 : ℝ) ≤ Real.exp (-8877/458752 : ℝ) ∧ Real.exp (-8877/458752 : ℝ) ≤ (196167138283/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490417845707/500000000000 : ℝ) ≤ (radius 7 (8877/65536 : ℝ)) ∧ (radius 7 (8877/65536 : ℝ)) ≤ (196167138283/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8877/65536 : ℝ)) (490417845707/500000000000 : ℝ) (196167138283/200000000000 : ℝ) (97418358699/500000000000 : ℝ) (48709179351/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8877/65536 : ℝ)) (490417845707/500000000000 : ℝ) (196167138283/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490417845707/500000000000 : ℝ) (196167138283/200000000000 : ℝ) (990417845707/1000000000000 : ℝ) (247604461427/250000000000 : ℝ) (49518574581/50000000000 : ℝ) (990371491621/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 1 (990417845707/1000000000000 : ℝ) (247604461427/250000000000 : ℝ) (49518574581/50000000000 : ℝ) (990371491621/1000000000000 : ℝ) (990394668663/1000000000000 : ℝ) (198078933733/200000000000 : ℝ) (123799333549/125000000000 : ℝ) (495197334197/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 2 (990394668663/1000000000000 : ℝ) (198078933733/200000000000 : ℝ) (123799333549/125000000000 : ℝ) (495197334197/500000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 3 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 4 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 5 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 6 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8877/65536 : ℝ)) 7 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8877/65536 : ℝ))) (97418358699/500000000000 : ℝ) (48709179351/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97418358699/500000000000 : ℝ) (48709179351/250000000000 : ℝ) (597418358699/1000000000000 : ℝ) (298709179351/500000000000 : ℝ) (441403123457/1000000000000 : ℝ) (88280624693/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 1 (597418358699/1000000000000 : ℝ) (298709179351/500000000000 : ℝ) (441403123457/1000000000000 : ℝ) (88280624693/200000000000 : ℝ) (259705370539/500000000000 : ℝ) (129852685271/250000000000 : ℝ) (513519551273/1000000000000 : ℝ) (6418994391/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 2 (259705370539/500000000000 : ℝ) (129852685271/250000000000 : ℝ) (513519551273/1000000000000 : ℝ) (6418994391/12500000000 : ℝ) (20658605847/40000000000 : ℝ) (258232573091/500000000000 : ℝ) (516456746189/1000000000000 : ℝ) (516456746197/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 3 (20658605847/40000000000 : ℝ) (258232573091/500000000000 : ℝ) (516456746189/1000000000000 : ℝ) (516456746197/1000000000000 : ℝ) (258230473091/500000000000 : ℝ) (51646094619/100000000000 : ℝ) (129115236541/250000000000 : ℝ) (516460946173/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 4 (258230473091/500000000000 : ℝ) (51646094619/100000000000 : ℝ) (129115236541/250000000000 : ℝ) (516460946173/1000000000000 : ℝ) (516460946173/1000000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 5 (516460946173/1000000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 6 (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8877/65536 : ℝ))) 7 (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8877/65536 : ℝ)) hmem 8 (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8877/65536 : ℝ))) hcmem 8 (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8877/65536 : ℝ)) (990394668527/1000000000000 : ℝ) (99039466853/100000000000 : ℝ) (129115236543/250000000000 : ℝ) (258230473091/500000000000 : ℝ) (819122904189/1000000000000 : ℝ) (51195181513/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0266_exp_lower
  have heNumeric : (1009506187547/500000000000 : ℝ)/4 ≤ Real.exp (-2734743569957/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506187547/500000000000 : ℝ)/4 ≤ Real.exp ((2219/16384 : ℝ)-(51195181513/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2219/16384 : ℝ) (8877/65536 : ℝ) (51195181513/62500000000 : ℝ) (1009506187547/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0267; no trusted numerical premise.
theorem cover7_leaf0267_exp_radius : (997583860551883941/1000000000000000000 : ℝ) ≤ Real.exp ((-4439/229376 : ℝ)/8) ∧ Real.exp ((-4439/229376 : ℝ)/8) ≤ (498791930275941971/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4439/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0267_exp_lower : (229522295786283331/250000000000000000 : ℝ) ≤ Real.exp ((-10938975191651/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938975191651/16000000000000 : ℝ)/8) ≤ (36723567325805333/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938975191651/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0267_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012260033/1000000000000 : ℝ) ≤ 4*Real.exp (8877/65536 : ℝ)*Real.exp (-mu (radius 7 (4439/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012260033/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4439/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0267_exp_radius
  have hrNumeric : (245208388341/250000000000 : ℝ) ≤ Real.exp (-4439/229376 : ℝ) ∧ Real.exp (-4439/229376 : ℝ) ≤ (196166710673/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245208388341/250000000000 : ℝ) ≤ (radius 7 (4439/32768 : ℝ)) ∧ (radius 7 (4439/32768 : ℝ)) ≤ (196166710673/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4439/32768 : ℝ)) (245208388341/250000000000 : ℝ) (196166710673/200000000000 : ℝ) (12177967521/62500000000 : ℝ) (97423740171/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4439/32768 : ℝ)) (245208388341/250000000000 : ℝ) (196166710673/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245208388341/250000000000 : ℝ) (196166710673/200000000000 : ℝ) (495208388341/500000000000 : ℝ) (990416776683/1000000000000 : ℝ) (990370412201/1000000000000 : ℝ) (495185206101/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 1 (495208388341/500000000000 : ℝ) (990416776683/1000000000000 : ℝ) (990370412201/1000000000000 : ℝ) (495185206101/500000000000 : ℝ) (990393594441/1000000000000 : ℝ) (990393594443/1000000000000 : ℝ) (99039359417/100000000000 : ℝ) (247598398543/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 2 (990393594441/1000000000000 : ℝ) (990393594443/1000000000000 : ℝ) (99039359417/100000000000 : ℝ) (247598398543/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 3 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 4 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 5 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 6 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4439/32768 : ℝ)) 7 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4439/32768 : ℝ))) (12177967521/62500000000 : ℝ) (97423740171/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12177967521/62500000000 : ℝ) (97423740171/500000000000 : ℝ) (74677967521/125000000000 : ℝ) (597423740171/1000000000000 : ℝ) (220707657511/500000000000 : ℝ) (441415315029/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 1 (74677967521/125000000000 : ℝ) (597423740171/1000000000000 : ℝ) (220707657511/500000000000 : ℝ) (441415315029/1000000000000 : ℝ) (103883905519/200000000000 : ℝ) (1298548819/2500000000 : ℝ) (256764477911/500000000000 : ℝ) (128382238957/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 2 (103883905519/200000000000 : ℝ) (1298548819/2500000000 : ℝ) (256764477911/500000000000 : ℝ) (128382238957/250000000000 : ℝ) (129118560427/250000000000 : ℝ) (258237120857/500000000000 : ℝ) (32279115227/62500000000 : ℝ) (516465843639/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 3 (129118560427/250000000000 : ℝ) (258237120857/500000000000 : ℝ) (32279115227/62500000000 : ℝ) (516465843639/1000000000000 : ℝ) (51647004267/100000000000 : ℝ) (516470042677/1000000000000 : ℝ) (129117510663/250000000000 : ℝ) (25823502133/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 4 (51647004267/100000000000 : ℝ) (516470042677/1000000000000 : ℝ) (129117510663/250000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042661/1000000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 5 (516470042661/1000000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 6 (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4439/32768 : ℝ))) 7 (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4439/32768 : ℝ)) hmem 8 (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4439/32768 : ℝ))) hcmem 8 (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4439/32768 : ℝ)) (198078718861/200000000000 : ℝ) (247598398577/250000000000 : ℝ) (25823502133/50000000000 : ℝ) (516470042669/1000000000000 : ℝ) (12799034687/15625000000 : ℝ) (409569109993/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0267_exp_lower
  have heNumeric : (2019012260033/1000000000000 : ℝ)/4 ≤ Real.exp (-10938975191651/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012260033/1000000000000 : ℝ)/4 ≤ Real.exp ((8877/65536 : ℝ)-(409569109993/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8877/65536 : ℝ) (4439/32768 : ℝ) (409569109993/500000000000 : ℝ) (2019012260033/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0268; no trusted numerical premise.
theorem cover7_leaf0268_exp_radius : (997583588731890611/1000000000000000000 : ℝ) ≤ Real.exp ((-8879/458752 : ℝ)/8) ∧ Real.exp ((-8879/458752 : ℝ)/8) ≤ (249395897182972653/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8879/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0268_exp_lower : (459044588368668533/500000000000000000 : ℝ) ≤ Real.exp ((-5469488042513/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469488042513/8000000000000 : ℝ)/8) ≤ (918089176737337067/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469488042513/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0268_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012147299/1000000000000 : ℝ) ≤ 4*Real.exp (4439/32768 : ℝ)*Real.exp (-mu (radius 7 (8879/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012147299/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8879/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0268_exp_radius
  have hrNumeric : (980831415319/1000000000000 : ℝ) ≤ Real.exp (-8879/458752 : ℝ) ∧ Real.exp (-8879/458752 : ℝ) ≤ (24520785383/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980831415319/1000000000000 : ℝ) ≤ (radius 7 (8879/65536 : ℝ)) ∧ (radius 7 (8879/65536 : ℝ)) ≤ (24520785383/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8879/65536 : ℝ)) (980831415319/1000000000000 : ℝ) (24520785383/25000000000 : ℝ) (194858242631/1000000000000 : ℝ) (194858242637/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8879/65536 : ℝ)) (980831415319/1000000000000 : ℝ) (24520785383/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980831415319/1000000000000 : ℝ) (24520785383/25000000000 : ℝ) (990415707659/1000000000000 : ℝ) (49520785383/50000000000 : ℝ) (990369332783/1000000000000 : ℝ) (198073866557/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 1 (990415707659/1000000000000 : ℝ) (49520785383/50000000000 : ℝ) (990369332783/1000000000000 : ℝ) (198073866557/200000000000 : ℝ) (990392520221/1000000000000 : ℝ) (990392520223/1000000000000 : ℝ) (990392519949/1000000000000 : ℝ) (61899532497/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 2 (990392520221/1000000000000 : ℝ) (990392520223/1000000000000 : ℝ) (990392519949/1000000000000 : ℝ) (61899532497/62500000000 : ℝ) (198078504017/200000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 3 (198078504017/200000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 4 (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 5 (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 6 (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8879/65536 : ℝ)) 7 (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8879/65536 : ℝ))) (194858242631/1000000000000 : ℝ) (194858242637/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194858242631/1000000000000 : ℝ) (194858242637/1000000000000 : ℝ) (119485824263/200000000000 : ℝ) (597429121319/1000000000000 : ℝ) (441427505521/1000000000000 : ℝ) (441427505529/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 1 (119485824263/200000000000 : ℝ) (597429121319/1000000000000 : ℝ) (441427505521/1000000000000 : ℝ) (441427505529/1000000000000 : ℝ) (259714156709/500000000000 : ℝ) (32464269589/62500000000 : ℝ) (513538359567/1000000000000 : ℝ) (20541534383/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 2 (259714156709/500000000000 : ℝ) (32464269589/62500000000 : ℝ) (513538359567/1000000000000 : ℝ) (20541534383/40000000000 : ℝ) (129120834123/250000000000 : ℝ) (1032966673/2000000000 : ℝ) (258237470163/500000000000 : ℝ) (258237470167/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 3 (129120834123/250000000000 : ℝ) (1032966673/2000000000 : ℝ) (258237470163/500000000000 : ℝ) (258237470167/500000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138417/1000000000000 : ℝ) (516479138391/1000000000000 : ℝ) (645598923/1250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 4 (516479138409/1000000000000 : ℝ) (516479138417/1000000000000 : ℝ) (516479138391/1000000000000 : ℝ) (645598923/1250000000 : ℝ) (645598923/1250000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 5 (645598923/1250000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 6 (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8879/65536 : ℝ))) 7 (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8879/65536 : ℝ)) hmem 8 (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8879/65536 : ℝ))) hcmem 8 (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8879/65536 : ℝ)) (247598130021/250000000000 : ℝ) (123799065011/125000000000 : ℝ) (516479138399/1000000000000 : ℝ) (516479138409/1000000000000 : ℝ) (819153534591/1000000000000 : ℝ) (819153534611/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0268_exp_lower
  have heNumeric : (2019012147299/1000000000000 : ℝ)/4 ≤ Real.exp (-5469488042513/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012147299/1000000000000 : ℝ)/4 ≤ Real.exp ((4439/32768 : ℝ)-(819153534611/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4439/32768 : ℝ) (8879/65536 : ℝ) (819153534611/1000000000000 : ℝ) (2019012147299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0269; no trusted numerical premise.
theorem cover7_leaf0269_exp_radius : (498791658455985673/500000000000000000 : ℝ) ≤ Real.exp ((-555/28672 : ℝ)/8) ∧ Real.exp ((-555/28672 : ℝ)/8) ≤ (997583316911971347/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-555/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0269_exp_lower : (918089170461286647/1000000000000000000 : ℝ) ≤ Real.exp ((-10938976960033/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938976960033/16000000000000 : ℝ)/8) ≤ (114761146307660831/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938976960033/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0269_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753009221/250000000000 : ℝ) ≤ 4*Real.exp (8879/65536 : ℝ)*Real.exp (-mu (radius 7 (555/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (504753009221/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (555/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0269_exp_radius
  have hrNumeric : (490414638639/500000000000 : ℝ) ≤ Real.exp (-555/28672 : ℝ) ∧ Real.exp (-555/28672 : ℝ) ≤ (980829277279/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490414638639/500000000000 : ℝ) ≤ (radius 7 (555/4096 : ℝ)) ∧ (radius 7 (555/4096 : ℝ)) ≤ (980829277279/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (555/4096 : ℝ)) (490414638639/500000000000 : ℝ) (980829277279/1000000000000 : ℝ) (95150881/488281250 : ℝ) (97434502147/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (555/4096 : ℝ)) (490414638639/500000000000 : ℝ) (980829277279/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (555/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490414638639/500000000000 : ℝ) (980829277279/1000000000000 : ℝ) (990414638639/1000000000000 : ℝ) (12380182983/12500000000 : ℝ) (990368253367/1000000000000 : ℝ) (123796031671/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (555/4096 : ℝ)) 1 (990414638639/1000000000000 : ℝ) (12380182983/12500000000 : ℝ) (990368253367/1000000000000 : ℝ) (123796031671/125000000000 : ℝ) (990391446003/1000000000000 : ℝ) (247597861501/250000000000 : ℝ) (990391445731/1000000000000 : ℝ) (990391445733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (555/4096 : ℝ)) 2 (990391446003/1000000000000 : ℝ) (247597861501/250000000000 : ℝ) (990391445731/1000000000000 : ℝ) (990391445733/1000000000000 : ℝ) (990391445867/1000000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (555/4096 : ℝ)) 3 (990391445867/1000000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (555/4096 : ℝ)) 4 (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (555/4096 : ℝ)) 5 (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (555/4096 : ℝ)) 6 (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (555/4096 : ℝ)) 7 (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (555/4096 : ℝ))) (95150881/488281250 : ℝ) (97434502147/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95150881/488281250 : ℝ) (97434502147/500000000000 : ℝ) (583432131/976562500 : ℝ) (597434502147/1000000000000 : ℝ) (441439694961/1000000000000 : ℝ) (441439694969/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 1 (583432131/976562500 : ℝ) (597434502147/1000000000000 : ℝ) (441439694961/1000000000000 : ℝ) (441439694969/1000000000000 : ℝ) (64929637319/125000000000 : ℝ) (259718549279/500000000000 : ℝ) (128386940629/250000000000 : ℝ) (513547762523/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 2 (64929637319/125000000000 : ℝ) (259718549279/500000000000 : ℝ) (128386940629/250000000000 : ℝ) (513547762523/1000000000000 : ℝ) (258246215267/500000000000 : ℝ) (516492430541/1000000000000 : ℝ) (516484036277/1000000000000 : ℝ) (129121009071/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 3 (258246215267/500000000000 : ℝ) (516492430541/1000000000000 : ℝ) (516484036277/1000000000000 : ℝ) (129121009071/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (516488233413/1000000000000 : ℝ) (129122058347/250000000000 : ℝ) (129122058349/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 4 (103297646681/200000000000 : ℝ) (516488233413/1000000000000 : ℝ) (129122058347/250000000000 : ℝ) (129122058349/250000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 5 (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 6 (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (555/4096 : ℝ))) 7 (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (555/4096 : ℝ)) hmem 8 (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (555/4096 : ℝ))) hcmem 8 (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (555/4096 : ℝ)) (495195722933/500000000000 : ℝ) (990391445869/1000000000000 : ℝ) (129122058349/250000000000 : ℝ) (103297646681/200000000000 : ℝ) (81916884807/100000000000 : ℝ) (102396106011/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0269_exp_lower
  have heNumeric : (504753009221/250000000000 : ℝ)/4 ≤ Real.exp (-10938976960033/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753009221/250000000000 : ℝ)/4 ≤ Real.exp ((8879/65536 : ℝ)-(102396106011/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8879/65536 : ℝ) (555/4096 : ℝ) (102396106011/125000000000 : ℝ) (504753009221/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0270; no trusted numerical premise.
theorem cover7_leaf0270_exp_radius : (199516609018425229/200000000000000000 : ℝ) ≤ Real.exp ((-8881/458752 : ℝ)/8) ∧ Real.exp ((-8881/458752 : ℝ)/8) ≤ (498791522546063073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8881/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0270_exp_lower : (183617832863557079/200000000000000000 : ℝ) ≤ Real.exp ((-136737222707/200000000000 : ℝ)/8) ∧ Real.exp ((-136737222707/200000000000 : ℝ)/8) ≤ (229522291079446349/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136737222707/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0270_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2523764911/1250000000 : ℝ) ≤ 4*Real.exp (555/4096 : ℝ)*Real.exp (-mu (radius 7 (8881/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2523764911/1250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8881/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0270_exp_radius
  have hrNumeric : (490413569621/500000000000 : ℝ) ≤ Real.exp (-8881/458752 : ℝ) ∧ Real.exp (-8881/458752 : ℝ) ≤ (980827139243/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490413569621/500000000000 : ℝ) ≤ (radius 7 (8881/65536 : ℝ)) ∧ (radius 7 (8881/65536 : ℝ)) ≤ (980827139243/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8881/65536 : ℝ)) (490413569621/500000000000 : ℝ) (980827139243/1000000000000 : ℝ) (97439882651/500000000000 : ℝ) (48719941327/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8881/65536 : ℝ)) (490413569621/500000000000 : ℝ) (980827139243/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490413569621/500000000000 : ℝ) (980827139243/1000000000000 : ℝ) (990413569621/1000000000000 : ℝ) (495206784811/500000000000 : ℝ) (15474487093/15625000000 : ℝ) (990367173953/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 1 (990413569621/1000000000000 : ℝ) (495206784811/500000000000 : ℝ) (15474487093/15625000000 : ℝ) (990367173953/1000000000000 : ℝ) (495195185893/500000000000 : ℝ) (247597592947/250000000000 : ℝ) (495195185757/500000000000 : ℝ) (247597592879/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 2 (495195185893/500000000000 : ℝ) (247597592947/250000000000 : ℝ) (495195185757/500000000000 : ℝ) (247597592879/250000000000 : ℝ) (19807807433/20000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 3 (19807807433/20000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 4 (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 5 (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 6 (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8881/65536 : ℝ)) 7 (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8881/65536 : ℝ))) (97439882651/500000000000 : ℝ) (48719941327/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97439882651/500000000000 : ℝ) (48719941327/250000000000 : ℝ) (597439882651/1000000000000 : ℝ) (298719941327/500000000000 : ℝ) (441451883337/1000000000000 : ℝ) (88290376669/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 1 (597439882651/1000000000000 : ℝ) (298719941327/500000000000 : ℝ) (441451883337/1000000000000 : ℝ) (88290376669/200000000000 : ℝ) (259722941497/500000000000 : ℝ) (519445883/1000000000 : ℝ) (513557164663/1000000000000 : ℝ) (51355716467/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 2 (259722941497/500000000000 : ℝ) (519445883/1000000000 : ℝ) (513557164663/1000000000000 : ℝ) (51355716467/100000000000 : ℝ) (129125380957/250000000000 : ℝ) (103300304767/200000000000 : ℝ) (12912328287/25000000000 : ℝ) (516493131487/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 3 (129125380957/250000000000 : ℝ) (103300304767/200000000000 : ℝ) (12912328287/25000000000 : ℝ) (516493131487/1000000000000 : ℝ) (258248663827/500000000000 : ℝ) (516497327661/1000000000000 : ℝ) (129124331909/250000000000 : ℝ) (129124331911/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 4 (258248663827/500000000000 : ℝ) (516497327661/1000000000000 : ℝ) (129124331909/250000000000 : ℝ) (129124331911/250000000000 : ℝ) (103299465529/200000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 5 (103299465529/200000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 6 (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8881/65536 : ℝ))) 7 (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8881/65536 : ℝ)) hmem 8 (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8881/65536 : ℝ))) hcmem 8 (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8881/65536 : ℝ)) (990390371649/1000000000000 : ℝ) (247597592913/250000000000 : ℝ) (129124331911/250000000000 : ℝ) (516497327653/1000000000000 : ℝ) (102398020049/125000000000 : ℝ) (81918416041/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0270_exp_lower
  have heNumeric : (2523764911/1250000000 : ℝ)/4 ≤ Real.exp (-136737222707/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2523764911/1250000000 : ℝ)/4 ≤ Real.exp ((555/4096 : ℝ)-(81918416041/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (555/4096 : ℝ) (8881/65536 : ℝ) (81918416041/100000000000 : ℝ) (2523764911/1250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0271; no trusted numerical premise.
theorem cover7_leaf0271_exp_radius : (99758277327235501/100000000000000000 : ℝ) ≤ Real.exp ((-4441/229376 : ℝ)/8) ∧ Real.exp ((-4441/229376 : ℝ)/8) ≤ (997582773272355011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4441/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0271_exp_lower : (114761144788325473/125000000000000000 : ℝ) ≤ Real.exp ((-10938978654639/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938978654639/16000000000000 : ℝ)/8) ≤ (183617831661320757/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938978654639/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0271_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752955761/250000000000 : ℝ) ≤ 4*Real.exp (8881/65536 : ℝ)*Real.exp (-mu (radius 7 (4441/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504752955761/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4441/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0271_exp_radius
  have hrNumeric : (980825001211/1000000000000 : ℝ) ≤ Real.exp (-4441/229376 : ℝ) ∧ Real.exp (-4441/229376 : ℝ) ≤ (245206250303/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980825001211/1000000000000 : ℝ) ≤ (radius 7 (4441/32768 : ℝ)) ∧ (radius 7 (4441/32768 : ℝ)) ≤ (245206250303/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4441/32768 : ℝ)) (980825001211/1000000000000 : ℝ) (245206250303/250000000000 : ℝ) (194890525673/1000000000000 : ℝ) (2436131571/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4441/32768 : ℝ)) (980825001211/1000000000000 : ℝ) (245206250303/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980825001211/1000000000000 : ℝ) (245206250303/250000000000 : ℝ) (198082500121/200000000000 : ℝ) (495206250303/500000000000 : ℝ) (495183047269/500000000000 : ℝ) (990366094539/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 1 (198082500121/200000000000 : ℝ) (495206250303/500000000000 : ℝ) (495183047269/500000000000 : ℝ) (990366094539/1000000000000 : ℝ) (990389297571/1000000000000 : ℝ) (990389297573/1000000000000 : ℝ) (990389297299/1000000000000 : ℝ) (990389297301/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 2 (990389297571/1000000000000 : ℝ) (990389297573/1000000000000 : ℝ) (990389297299/1000000000000 : ℝ) (990389297301/1000000000000 : ℝ) (198077859487/200000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 3 (198077859487/200000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 4 (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 5 (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 6 (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4441/32768 : ℝ)) 7 (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4441/32768 : ℝ))) (194890525673/1000000000000 : ℝ) (2436131571/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194890525673/1000000000000 : ℝ) (2436131571/12500000000 : ℝ) (149361315709/250000000000 : ℝ) (14936131571/25000000000 : ℝ) (441464070647/1000000000000 : ℝ) (862234513/1953125000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 1 (149361315709/250000000000 : ℝ) (14936131571/25000000000 : ℝ) (441464070647/1000000000000 : ℝ) (862234513/1953125000 : ℝ) (519454666741/1000000000000 : ℝ) (129863666687/250000000000 : ℝ) (513566566007/1000000000000 : ℝ) (102713313203/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 2 (519454666741/1000000000000 : ℝ) (129863666687/250000000000 : ℝ) (513566566007/1000000000000 : ℝ) (102713313203/200000000000 : ℝ) (258255308187/500000000000 : ℝ) (258255308191/500000000000 : ℝ) (516502225933/1000000000000 : ℝ) (258251112971/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 3 (258255308187/500000000000 : ℝ) (258255308191/500000000000 : ℝ) (516502225933/1000000000000 : ℝ) (258251112971/500000000000 : ℝ) (516506421153/1000000000000 : ℝ) (258253210581/500000000000 : ℝ) (32281651321/62500000000 : ℝ) (103301284229/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 4 (516506421153/1000000000000 : ℝ) (258253210581/500000000000 : ℝ) (32281651321/62500000000 : ℝ) (103301284229/200000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 5 (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 6 (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4441/32768 : ℝ))) 7 (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4441/32768 : ℝ)) hmem 8 (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4441/32768 : ℝ))) hcmem 8 (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4441/32768 : ℝ)) (495194648717/500000000000 : ℝ) (990389297437/1000000000000 : ℝ) (64563302643/125000000000 : ℝ) (258253210577/500000000000 : ℝ) (819199471559/1000000000000 : ℝ) (819199471579/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0271_exp_lower
  have heNumeric : (504752955761/250000000000 : ℝ)/4 ≤ Real.exp (-10938978654639/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752955761/250000000000 : ℝ)/4 ≤ Real.exp ((8881/65536 : ℝ)-(819199471579/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8881/65536 : ℝ) (4441/32768 : ℝ) (819199471579/1000000000000 : ℝ) (504752955761/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0272; no trusted numerical premise.
theorem cover7_leaf0272_exp_radius : (49879125072632897/50000000000000000 : ℝ) ≤ Real.exp ((-1269/65536 : ℝ)/8) ∧ Real.exp ((-1269/65536 : ℝ)/8) ≤ (997582501452657941/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1269/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0272_exp_lower : (114761144053525107/125000000000000000 : ℝ) ≤ Real.exp ((-5469489737103/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469489737103/8000000000000 : ℝ)/8) ≤ (918089152428200857/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469489737103/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0272_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16152093757/8000000000 : ℝ) ≤ 4*Real.exp (4441/32768 : ℝ)*Real.exp (-mu (radius 7 (8883/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (16152093757/8000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8883/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0272_exp_radius
  have hrNumeric : (196164572637/200000000000 : ℝ) ≤ Real.exp (-1269/65536 : ℝ) ∧ Real.exp (-1269/65536 : ℝ) ≤ (490411431593/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196164572637/200000000000 : ℝ) ≤ (radius 7 (8883/65536 : ℝ)) ∧ (radius 7 (8883/65536 : ℝ)) ≤ (490411431593/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8883/65536 : ℝ)) (196164572637/200000000000 : ℝ) (490411431593/500000000000 : ℝ) (97450642701/500000000000 : ℝ) (6090665169/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8883/65536 : ℝ)) (196164572637/200000000000 : ℝ) (490411431593/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196164572637/200000000000 : ℝ) (490411431593/500000000000 : ℝ) (123801428949/125000000000 : ℝ) (990411431593/1000000000000 : ℝ) (7922920121/8000000000 : ℝ) (990365015127/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 1 (123801428949/125000000000 : ℝ) (990411431593/1000000000000 : ℝ) (7922920121/8000000000 : ℝ) (990365015127/1000000000000 : ℝ) (495194111679/500000000000 : ℝ) (1547481599/1562500000 : ℝ) (495194111543/500000000000 : ℝ) (990388223089/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 2 (495194111679/500000000000 : ℝ) (1547481599/1562500000 : ℝ) (495194111543/500000000000 : ℝ) (990388223089/1000000000000 : ℝ) (495194111611/500000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 3 (495194111611/500000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 4 (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 5 (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 6 (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8883/65536 : ℝ)) 7 (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8883/65536 : ℝ))) (97450642701/500000000000 : ℝ) (6090665169/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97450642701/500000000000 : ℝ) (6090665169/31250000000 : ℝ) (597450642701/1000000000000 : ℝ) (37340665169/62500000000 : ℝ) (220738128447/500000000000 : ℝ) (220738128451/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 1 (597450642701/1000000000000 : ℝ) (37340665169/62500000000 : ℝ) (220738128447/500000000000 : ℝ) (220738128451/500000000000 : ℝ) (519463449797/1000000000000 : ℝ) (519463449803/1000000000000 : ℝ) (10271519331/20000000000 : ℝ) (513575966557/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 2 (519463449797/1000000000000 : ℝ) (519463449803/1000000000000 : ℝ) (10271519331/20000000000 : ℝ) (513575966557/1000000000000 : ℝ) (516519708173/1000000000000 : ℝ) (25825985409/50000000000 : ℝ) (12912782991/25000000000 : ℝ) (16140978739/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 3 (516519708173/1000000000000 : ℝ) (25825985409/50000000000 : ℝ) (12912782991/25000000000 : ℝ) (16140978739/31250000000 : ℝ) (258257756953/500000000000 : ℝ) (258257756957/500000000000 : ℝ) (516515513889/1000000000000 : ℝ) (516515513897/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 4 (258257756953/500000000000 : ℝ) (258257756957/500000000000 : ℝ) (516515513889/1000000000000 : ℝ) (516515513897/1000000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 5 (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 6 (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8883/65536 : ℝ))) 7 (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8883/65536 : ℝ)) hmem 8 (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8883/65536 : ℝ))) hcmem 8 (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8883/65536 : ℝ)) (990388223221/1000000000000 : ℝ) (39615528929/40000000000 : ℝ) (516515513897/1000000000000 : ℝ) (258257756953/500000000000 : ℝ) (819214781573/1000000000000 : ℝ) (819214781591/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0272_exp_lower
  have heNumeric : (16152093757/8000000000 : ℝ)/4 ≤ Real.exp (-5469489737103/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16152093757/8000000000 : ℝ)/4 ≤ Real.exp ((4441/32768 : ℝ)-(819214781591/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4441/32768 : ℝ) (8883/65536 : ℝ) (819214781591/1000000000000 : ℝ) (16152093757/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0273; no trusted numerical premise.
theorem cover7_leaf0273_exp_radius : (199516445926606987/200000000000000000 : ℝ) ≤ Real.exp ((-2221/114688 : ℝ)/8) ∧ Real.exp ((-2221/114688 : ℝ)/8) ≤ (124697778704129367/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2221/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0273_exp_lower : (918089146681084713/1000000000000000000 : ℝ) ≤ Real.exp ((-10938980275469/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938980275469/16000000000000 : ℝ)/8) ≤ (459044573340542357/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938980275469/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0273_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802323703/200000000000 : ℝ) ≤ 4*Real.exp (8883/65536 : ℝ)*Real.exp (-mu (radius 7 (2221/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403802323703/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2221/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0273_exp_radius
  have hrNumeric : (980820725163/1000000000000 : ℝ) ≤ Real.exp (-2221/114688 : ℝ) ∧ Real.exp (-2221/114688 : ℝ) ≤ (245205181291/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980820725163/1000000000000 : ℝ) ≤ (radius 7 (2221/16384 : ℝ)) ∧ (radius 7 (2221/16384 : ℝ)) ≤ (245205181291/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2221/16384 : ℝ)) (980820725163/1000000000000 : ℝ) (245205181291/250000000000 : ℝ) (194912044493/1000000000000 : ℝ) (194912044499/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2221/16384 : ℝ)) (980820725163/1000000000000 : ℝ) (245205181291/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980820725163/1000000000000 : ℝ) (245205181291/250000000000 : ℝ) (990410362581/1000000000000 : ℝ) (495205181291/500000000000 : ℝ) (495181967857/500000000000 : ℝ) (198072787143/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 1 (990410362581/1000000000000 : ℝ) (495205181291/500000000000 : ℝ) (495181967857/500000000000 : ℝ) (198072787143/200000000000 : ℝ) (990387149147/1000000000000 : ℝ) (990387149149/1000000000000 : ℝ) (7923097191/8000000000 : ℝ) (990387148877/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 2 (990387149147/1000000000000 : ℝ) (990387149149/1000000000000 : ℝ) (7923097191/8000000000 : ℝ) (990387148877/1000000000000 : ℝ) (990387149011/1000000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 3 (990387149011/1000000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 4 (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 5 (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 6 (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2221/16384 : ℝ)) 7 (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2221/16384 : ℝ))) (194912044493/1000000000000 : ℝ) (194912044499/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194912044493/1000000000000 : ℝ) (194912044499/1000000000000 : ℝ) (298728011123/500000000000 : ℝ) (2389824089/4000000000 : ℝ) (441488442083/1000000000000 : ℝ) (44148844209/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 1 (298728011123/500000000000 : ℝ) (2389824089/4000000000 : ℝ) (441488442083/1000000000000 : ℝ) (44148844209/100000000000 : ℝ) (129868058041/250000000000 : ℝ) (51947223217/100000000000 : ℝ) (513585366297/1000000000000 : ℝ) (513585366303/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 2 (129868058041/250000000000 : ℝ) (51947223217/100000000000 : ℝ) (513585366297/1000000000000 : ℝ) (513585366303/1000000000000 : ℝ) (51652879923/100000000000 : ℝ) (516528799237/1000000000000 : ℝ) (129130103151/250000000000 : ℝ) (516520412611/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 3 (51652879923/100000000000 : ℝ) (516528799237/1000000000000 : ℝ) (129130103151/250000000000 : ℝ) (516520412611/1000000000000 : ℝ) (516524605917/1000000000000 : ℝ) (129131151481/250000000000 : ℝ) (516524605899/1000000000000 : ℝ) (516524605907/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 4 (516524605917/1000000000000 : ℝ) (129131151481/250000000000 : ℝ) (516524605899/1000000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151477/250000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 5 (129131151477/250000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 6 (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2221/16384 : ℝ))) 7 (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2221/16384 : ℝ)) hmem 8 (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2221/16384 : ℝ))) hcmem 8 (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2221/16384 : ℝ)) (99038714901/100000000000 : ℝ) (990387149013/1000000000000 : ℝ) (516524605907/1000000000000 : ℝ) (129131151479/250000000000 : ℝ) (819230090441/1000000000000 : ℝ) (819230090459/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0273_exp_lower
  have heNumeric : (403802323703/200000000000 : ℝ)/4 ≤ Real.exp (-10938980275469/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802323703/200000000000 : ℝ)/4 ≤ Real.exp ((8883/65536 : ℝ)-(819230090459/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8883/65536 : ℝ) (2221/16384 : ℝ) (819230090459/1000000000000 : ℝ) (403802323703/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0274; no trusted numerical premise.
theorem cover7_leaf0274_exp_radius : (199516391562697199/200000000000000000 : ℝ) ≤ Real.exp ((-8885/458752 : ℝ)/8) ∧ Real.exp ((-8885/458752 : ℝ)/8) ≤ (249395489453371499/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8885/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0274_exp_lower : (459044570533201483/500000000000000000 : ℝ) ≤ Real.exp ((-2734745264567/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734745264567/4000000000000 : ℝ)/8) ≤ (918089141066402967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734745264567/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0274_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802303947/200000000000 : ℝ) ≤ 4*Real.exp (2221/16384 : ℝ)*Real.exp (-mu (radius 7 (8885/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403802303947/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8885/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0274_exp_radius
  have hrNumeric : (490409293573/500000000000 : ℝ) ≤ Real.exp (-8885/458752 : ℝ) ∧ Real.exp (-8885/458752 : ℝ) ≤ (980818587147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490409293573/500000000000 : ℝ) ≤ (radius 7 (8885/65536 : ℝ)) ∧ (radius 7 (8885/65536 : ℝ)) ≤ (980818587147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8885/65536 : ℝ)) (490409293573/500000000000 : ℝ) (980818587147/1000000000000 : ℝ) (97461401471/500000000000 : ℝ) (48730700737/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8885/65536 : ℝ)) (490409293573/500000000000 : ℝ) (980818587147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490409293573/500000000000 : ℝ) (980818587147/1000000000000 : ℝ) (990409293573/1000000000000 : ℝ) (495204646787/500000000000 : ℝ) (990362856303/1000000000000 : ℝ) (198072571261/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 1 (990409293573/1000000000000 : ℝ) (495204646787/500000000000 : ℝ) (990362856303/1000000000000 : ℝ) (198072571261/200000000000 : ℝ) (495193037469/500000000000 : ℝ) (49519303747/50000000000 : ℝ) (198077214933/200000000000 : ℝ) (247596518667/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 2 (495193037469/500000000000 : ℝ) (49519303747/50000000000 : ℝ) (198077214933/200000000000 : ℝ) (247596518667/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 3 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 4 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 5 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 6 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8885/65536 : ℝ)) 7 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8885/65536 : ℝ))) (97461401471/500000000000 : ℝ) (48730700737/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97461401471/500000000000 : ℝ) (48730700737/250000000000 : ℝ) (597461401471/1000000000000 : ℝ) (298730700737/500000000000 : ℝ) (441500626207/1000000000000 : ℝ) (88300125243/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 1 (597461401471/1000000000000 : ℝ) (298730700737/500000000000 : ℝ) (441500626207/1000000000000 : ℝ) (88300125243/200000000000 : ℝ) (519481013839/1000000000000 : ℝ) (103896202769/200000000000 : ℝ) (513594765241/1000000000000 : ℝ) (8024918207/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 2 (519481013839/1000000000000 : ℝ) (103896202769/200000000000 : ℝ) (513594765241/1000000000000 : ℝ) (8024918207/15625000000 : ℝ) (25826894477/50000000000 : ℝ) (516537889547/1000000000000 : ℝ) (25826475241/50000000000 : ℝ) (516529504827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 3 (25826894477/50000000000 : ℝ) (516537889547/1000000000000 : ℝ) (25826475241/50000000000 : ℝ) (516529504827/1000000000000 : ℝ) (25826684859/50000000000 : ℝ) (516533697187/1000000000000 : ℝ) (258266848581/500000000000 : ℝ) (51653369717/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 4 (25826684859/50000000000 : ℝ) (516533697187/1000000000000 : ℝ) (258266848581/500000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697171/1000000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 5 (516533697171/1000000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 6 (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8885/65536 : ℝ))) 7 (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8885/65536 : ℝ)) hmem 8 (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8885/65536 : ℝ))) hcmem 8 (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8885/65536 : ℝ)) (990386074801/1000000000000 : ℝ) (247596518701/250000000000 : ℝ) (51653369717/100000000000 : ℝ) (516533697179/1000000000000 : ℝ) (163849079631/200000000000 : ℝ) (819245398173/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0274_exp_lower
  have heNumeric : (403802303947/200000000000 : ℝ)/4 ≤ Real.exp (-2734745264567/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802303947/200000000000 : ℝ)/4 ≤ Real.exp ((2221/16384 : ℝ)-(819245398173/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2221/16384 : ℝ) (8885/65536 : ℝ) (819245398173/1000000000000 : ℝ) (403802303947/200000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0250_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0250_certificate
#check SmaleRate.Proofs.cover7_leaf0251_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0251_certificate
#check SmaleRate.Proofs.cover7_leaf0252_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0252_certificate
#check SmaleRate.Proofs.cover7_leaf0253_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0253_certificate
#check SmaleRate.Proofs.cover7_leaf0254_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0254_certificate
#check SmaleRate.Proofs.cover7_leaf0255_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0255_certificate
#check SmaleRate.Proofs.cover7_leaf0256_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0256_certificate
#check SmaleRate.Proofs.cover7_leaf0257_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0257_certificate
#check SmaleRate.Proofs.cover7_leaf0258_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0258_certificate
#check SmaleRate.Proofs.cover7_leaf0259_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0259_certificate
#check SmaleRate.Proofs.cover7_leaf0260_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0260_certificate
#check SmaleRate.Proofs.cover7_leaf0261_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0261_certificate
#check SmaleRate.Proofs.cover7_leaf0262_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0262_certificate
#check SmaleRate.Proofs.cover7_leaf0263_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0263_certificate
#check SmaleRate.Proofs.cover7_leaf0264_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0264_certificate
#check SmaleRate.Proofs.cover7_leaf0265_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0265_certificate
#check SmaleRate.Proofs.cover7_leaf0266_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0266_certificate
#check SmaleRate.Proofs.cover7_leaf0267_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0267_certificate
#check SmaleRate.Proofs.cover7_leaf0268_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0268_certificate
#check SmaleRate.Proofs.cover7_leaf0269_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0269_certificate
#check SmaleRate.Proofs.cover7_leaf0270_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0270_certificate
#check SmaleRate.Proofs.cover7_leaf0271_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0271_certificate
#check SmaleRate.Proofs.cover7_leaf0272_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0272_certificate
#check SmaleRate.Proofs.cover7_leaf0273_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0273_certificate
#check SmaleRate.Proofs.cover7_leaf0274_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0274_certificate
