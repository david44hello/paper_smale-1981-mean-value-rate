/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1700; no trusted numerical premise.
theorem cover8_leaf1700_exp_radius : (997729023008660901/1000000000000000000 : ℝ) ≤ Real.exp ((-149/8192 : ℝ)/8) ∧ Real.exp ((-149/8192 : ℝ)/8) ≤ (498864511504330451/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-149/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1700_exp_lower : (920147537317339977/1000000000000000000 : ℝ) ≤ Real.exp ((-665770041177/1000000000000 : ℝ)/8) ∧ Real.exp ((-665770041177/1000000000000 : ℝ)/8) ≤ (460073768658669989/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665770041177/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1700_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205551067339/100000000000 : ℝ) ≤ 4*Real.exp (297/2048 : ℝ)*Real.exp (-mu (radius 8 (149/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (205551067339/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (149/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1700_exp_radius
  have hrNumeric : (490987967733/500000000000 : ℝ) ≤ Real.exp (-149/8192 : ℝ) ∧ Real.exp (-149/8192 : ℝ) ≤ (981975935467/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490987967733/500000000000 : ℝ) ≤ (radius 8 (149/1024 : ℝ)) ∧ (radius 8 (149/1024 : ℝ)) ≤ (981975935467/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (149/1024 : ℝ)) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (149/1024 : ℝ)) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (149/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) (990987967733/1000000000000 : ℝ) (495493983867/500000000000 : ℝ) (990946989231/1000000000000 : ℝ) (61934186827/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (149/1024 : ℝ)) 1 (990987967733/1000000000000 : ℝ) (495493983867/500000000000 : ℝ) (990946989231/1000000000000 : ℝ) (61934186827/62500000000 : ℝ) (495483739241/500000000000 : ℝ) (990967478483/1000000000000 : ℝ) (99096747827/100000000000 : ℝ) (483870839/488281250 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (149/1024 : ℝ)) 2 (495483739241/500000000000 : ℝ) (990967478483/1000000000000 : ℝ) (99096747827/100000000000 : ℝ) (483870839/488281250 : ℝ) (123870934797/125000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (149/1024 : ℝ)) 3 (123870934797/125000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (149/1024 : ℝ)) 4 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (149/1024 : ℝ)) 5 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (149/1024 : ℝ)) 6 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (149/1024 : ℝ)) 7 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (149/1024 : ℝ))) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ) (74312874029/125000000000 : ℝ) (148625748059/250000000000 : ℝ) (434748185119/1000000000000 : ℝ) (434748185127/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 1 (74312874029/125000000000 : ℝ) (148625748059/250000000000 : ℝ) (434748185119/1000000000000 : ℝ) (434748185127/1000000000000 : ℝ) (20585023547/40000000000 : ℝ) (257312794341/500000000000 : ℝ) (508388726193/1000000000000 : ℝ) (2541943631/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 2 (20585023547/40000000000 : ℝ) (257312794341/500000000000 : ℝ) (508388726193/1000000000000 : ℝ) (2541943631/5000000000 : ℝ) (255753578717/500000000000 : ℝ) (511507157441/1000000000000 : ℝ) (255748825751/500000000000 : ℝ) (51149765151/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 3 (255753578717/500000000000 : ℝ) (511507157441/1000000000000 : ℝ) (255748825751/500000000000 : ℝ) (51149765151/100000000000 : ℝ) (127875601117/250000000000 : ℝ) (127875601119/250000000000 : ℝ) (102300480889/200000000000 : ℝ) (255751202227/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 4 (127875601117/250000000000 : ℝ) (127875601119/250000000000 : ℝ) (102300480889/200000000000 : ℝ) (255751202227/500000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 5 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 6 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (149/1024 : ℝ))) 7 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (149/1024 : ℝ)) hmem 8 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (149/1024 : ℝ))) hcmem 8 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (149/1024 : ℝ)) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (810789572409/1000000000000 : ℝ) (810789572427/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1700_exp_lower
  have heNumeric : (205551067339/100000000000 : ℝ)/4 ≤ Real.exp (-665770041177/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205551067339/100000000000 : ℝ)/4 ≤ Real.exp ((297/2048 : ℝ)-(810789572427/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (297/2048 : ℝ) (149/1024 : ℝ) (810789572427/1000000000000 : ℝ) (205551067339/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1701; no trusted numerical premise.
theorem cover8_leaf1701_exp_radius : (15589397046396043/15625000000000000 : ℝ) ≤ Real.exp ((-299/16384 : ℝ)/8) ∧ Real.exp ((-299/16384 : ℝ)/8) ≤ (997721410969346753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-299/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1701_exp_lower : (230038085314384121/250000000000000000 : ℝ) ≤ Real.exp ((-665728274591/1000000000000 : ℝ)/8) ∧ Real.exp ((-665728274591/1000000000000 : ℝ)/8) ≤ (184030468251507297/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665728274591/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1701_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027798263423/500000000000 : ℝ) ≤ 4*Real.exp (149/1024 : ℝ)*Real.exp (-mu (radius 8 (299/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027798263423/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (299/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1701_exp_radius
  have hrNumeric : (981916002241/1000000000000 : ℝ) ≤ Real.exp (-299/16384 : ℝ) ∧ Real.exp (-299/16384 : ℝ) ≤ (490958001121/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981916002241/1000000000000 : ℝ) ≤ (radius 8 (299/2048 : ℝ)) ∧ (radius 8 (299/2048 : ℝ)) ≤ (490958001121/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (299/2048 : ℝ)) (981916002241/1000000000000 : ℝ) (490958001121/500000000000 : ℝ) (94658550249/500000000000 : ℝ) (23664637563/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (299/2048 : ℝ)) (981916002241/1000000000000 : ℝ) (490958001121/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (299/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981916002241/1000000000000 : ℝ) (490958001121/500000000000 : ℝ) (6193487507/6250000000 : ℝ) (990958001121/1000000000000 : ℝ) (99091674839/100000000000 : ℝ) (123864593549/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (299/2048 : ℝ)) 1 (6193487507/6250000000 : ℝ) (990958001121/1000000000000 : ℝ) (99091674839/100000000000 : ℝ) (123864593549/125000000000 : ℝ) (198187474951/200000000000 : ℝ) (990937374757/1000000000000 : ℝ) (49546868727/50000000000 : ℝ) (495468687271/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (299/2048 : ℝ)) 2 (198187474951/200000000000 : ℝ) (990937374757/1000000000000 : ℝ) (49546868727/50000000000 : ℝ) (495468687271/500000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (299/2048 : ℝ)) 3 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (299/2048 : ℝ)) 4 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (299/2048 : ℝ)) 5 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (299/2048 : ℝ)) 6 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (299/2048 : ℝ)) 7 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (299/2048 : ℝ))) (94658550249/500000000000 : ℝ) (23664637563/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94658550249/500000000000 : ℝ) (23664637563/125000000000 : ℝ) (594658550249/1000000000000 : ℝ) (148664637563/250000000000 : ℝ) (435105849763/1000000000000 : ℝ) (43510584977/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 1 (594658550249/1000000000000 : ℝ) (148664637563/250000000000 : ℝ) (435105849763/1000000000000 : ℝ) (43510584977/100000000000 : ℝ) (257441100003/500000000000 : ℝ) (514882200011/1000000000000 : ℝ) (101732868597/200000000000 : ℝ) (508664342991/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 2 (257441100003/500000000000 : ℝ) (514882200011/1000000000000 : ℝ) (101732868597/200000000000 : ℝ) (508664342991/1000000000000 : ℝ) (102354654299/200000000000 : ℝ) (511773271501/1000000000000 : ℝ) (511763828323/1000000000000 : ℝ) (51176382833/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 3 (102354654299/200000000000 : ℝ) (511773271501/1000000000000 : ℝ) (511763828323/1000000000000 : ℝ) (51176382833/100000000000 : ℝ) (511768549909/1000000000000 : ℝ) (127942137479/250000000000 : ℝ) (511768549887/1000000000000 : ℝ) (255884274947/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 4 (511768549909/1000000000000 : ℝ) (127942137479/250000000000 : ℝ) (511768549887/1000000000000 : ℝ) (255884274947/500000000000 : ℝ) (255884274949/500000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 5 (255884274949/500000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 6 (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (299/2048 : ℝ))) 7 (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (299/2048 : ℝ)) hmem 8 (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (299/2048 : ℝ))) hcmem 8 (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (299/2048 : ℝ)) (990937374647/1000000000000 : ℝ) (19818747493/20000000000 : ℝ) (511768549897/1000000000000 : ℝ) (102353709981/200000000000 : ℝ) (405618043537/500000000000 : ℝ) (811236087091/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1701_exp_lower
  have heNumeric : (1027798263423/500000000000 : ℝ)/4 ≤ Real.exp (-665728274591/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027798263423/500000000000 : ℝ)/4 ≤ Real.exp ((149/1024 : ℝ)-(811236087091/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (149/1024 : ℝ) (299/2048 : ℝ) (811236087091/1000000000000 : ℝ) (1027798263423/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1702; no trusted numerical premise.
theorem cover8_leaf1702_exp_radius : (62357112436756727/62500000000000000 : ℝ) ≤ Real.exp ((-75/4096 : ℝ)/8) ∧ Real.exp ((-75/4096 : ℝ)/8) ≤ (997713798988107633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-75/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1702_exp_lower : (920157260390724259/1000000000000000000 : ℝ) ≤ Real.exp ((-166421376679/250000000000 : ℝ)/8) ∧ Real.exp ((-166421376679/250000000000 : ℝ)/8) ≤ (46007863019536213/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166421376679/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1702_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055684442221/1000000000000 : ℝ) ≤ 4*Real.exp (299/2048 : ℝ)*Real.exp (-mu (radius 8 (75/512 : ℝ))) ∧ (20549/10000 : ℝ) < (2055684442221/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (75/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1702_exp_radius
  have hrNumeric : (981856072673/1000000000000 : ℝ) ≤ Real.exp (-75/4096 : ℝ) ∧ Real.exp (-75/4096 : ℝ) ≤ (490928036337/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981856072673/1000000000000 : ℝ) ≤ (radius 8 (75/512 : ℝ)) ∧ (radius 8 (75/512 : ℝ)) ≤ (490928036337/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (75/512 : ℝ)) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (75/512 : ℝ)) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (75/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) (61933002271/62500000000 : ℝ) (990928036337/1000000000000 : ℝ) (123860813559/125000000000 : ℝ) (495443254237/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (75/512 : ℝ)) 1 (61933002271/62500000000 : ℝ) (990928036337/1000000000000 : ℝ) (123860813559/125000000000 : ℝ) (495443254237/500000000000 : ℝ) (247726818101/250000000000 : ℝ) (495453636203/500000000000 : ℝ) (495453636093/500000000000 : ℝ) (247726818047/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (75/512 : ℝ)) 2 (247726818101/250000000000 : ℝ) (495453636203/500000000000 : ℝ) (495453636093/500000000000 : ℝ) (247726818047/250000000000 : ℝ) (198181454459/200000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (75/512 : ℝ)) 3 (198181454459/200000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (75/512 : ℝ)) 4 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (75/512 : ℝ)) 5 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (75/512 : ℝ)) 6 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (75/512 : ℝ)) 7 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (75/512 : ℝ))) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ) (148703458527/250000000000 : ℝ) (594813834111/1000000000000 : ℝ) (435462591063/1000000000000 : ℝ) (435462591071/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 1 (148703458527/250000000000 : ℝ) (594813834111/1000000000000 : ℝ) (435462591063/1000000000000 : ℝ) (435462591071/1000000000000 : ℝ) (103027642517/200000000000 : ℝ) (515138212591/1000000000000 : ℝ) (254469631489/500000000000 : ℝ) (101787852597/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 2 (103027642517/200000000000 : ℝ) (515138212591/1000000000000 : ℝ) (254469631489/500000000000 : ℝ) (101787852597/200000000000 : ℝ) (512038737781/1000000000000 : ℝ) (128009684447/250000000000 : ℝ) (512029356819/1000000000000 : ℝ) (256014678413/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 3 (512038737781/1000000000000 : ℝ) (128009684447/250000000000 : ℝ) (512029356819/1000000000000 : ℝ) (256014678413/500000000000 : ℝ) (5120340473/10000000000 : ℝ) (512034047307/1000000000000 : ℝ) (256017023639/500000000000 : ℝ) (256017023643/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 4 (5120340473/10000000000 : ℝ) (512034047307/1000000000000 : ℝ) (256017023639/500000000000 : ℝ) (256017023643/500000000000 : ℝ) (512034047289/1000000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 5 (512034047289/1000000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 6 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (75/512 : ℝ))) 7 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (75/512 : ℝ)) hmem 8 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (75/512 : ℝ))) hcmem 8 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (75/512 : ℝ)) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (12682525007/15625000000 : ℝ) (405840800233/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1702_exp_lower
  have heNumeric : (2055684442221/1000000000000 : ℝ)/4 ≤ Real.exp (-166421376679/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055684442221/1000000000000 : ℝ)/4 ≤ Real.exp ((299/2048 : ℝ)-(405840800233/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (299/2048 : ℝ) (75/512 : ℝ) (405840800233/500000000000 : ℝ) (2055684442221/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1703; no trusted numerical premise.
theorem cover8_leaf1703_exp_radius : (997706187064943099/1000000000000000000 : ℝ) ≤ Real.exp ((-301/16384 : ℝ)/8) ∧ Real.exp ((-301/16384 : ℝ)/8) ≤ (9977061870649431/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-301/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1703_exp_lower : (184032458809728461/200000000000000000 : ℝ) ≤ Real.exp ((-332820871689/500000000000 : ℝ)/8) ∧ Real.exp ((-332820871689/500000000000 : ℝ)/8) ≤ (460081147024321153/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332820871689/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1703_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055774407803/1000000000000 : ℝ) ≤ 4*Real.exp (75/512 : ℝ)*Real.exp (-mu (radius 8 (301/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055774407803/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (301/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1703_exp_radius
  have hrNumeric : (981796146763/1000000000000 : ℝ) ≤ Real.exp (-301/16384 : ℝ) ∧ Real.exp (-301/16384 : ℝ) ≤ (245449036691/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981796146763/1000000000000 : ℝ) ≤ (radius 8 (301/2048 : ℝ)) ∧ (radius 8 (301/2048 : ℝ)) ≤ (245449036691/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (301/2048 : ℝ)) (981796146763/1000000000000 : ℝ) (245449036691/250000000000 : ℝ) (189937690307/1000000000000 : ℝ) (189937690313/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (301/2048 : ℝ)) (981796146763/1000000000000 : ℝ) (245449036691/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (301/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981796146763/1000000000000 : ℝ) (245449036691/250000000000 : ℝ) (990898073381/1000000000000 : ℝ) (495449036691/500000000000 : ℝ) (990856269477/1000000000000 : ℝ) (990856269479/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (301/2048 : ℝ)) 1 (990898073381/1000000000000 : ℝ) (495449036691/500000000000 : ℝ) (990856269477/1000000000000 : ℝ) (990856269479/1000000000000 : ℝ) (990877171429/1000000000000 : ℝ) (990877171431/1000000000000 : ℝ) (123859646401/125000000000 : ℝ) (990877171211/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (301/2048 : ℝ)) 2 (990877171429/1000000000000 : ℝ) (990877171431/1000000000000 : ℝ) (123859646401/125000000000 : ℝ) (990877171211/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (301/2048 : ℝ)) 3 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (301/2048 : ℝ)) 4 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (301/2048 : ℝ)) 5 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (301/2048 : ℝ)) 6 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (301/2048 : ℝ)) 7 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (301/2048 : ℝ))) (189937690307/1000000000000 : ℝ) (189937690313/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (189937690307/1000000000000 : ℝ) (189937690313/1000000000000 : ℝ) (594968845153/1000000000000 : ℝ) (594968845157/1000000000000 : ℝ) (435818414373/1000000000000 : ℝ) (435818414381/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 1 (594968845153/1000000000000 : ℝ) (594968845157/1000000000000 : ℝ) (435818414373/1000000000000 : ℝ) (435818414381/1000000000000 : ℝ) (515393629763/1000000000000 : ℝ) (515393629769/1000000000000 : ℝ) (127303372573/250000000000 : ℝ) (509213490299/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 2 (515393629763/1000000000000 : ℝ) (515393629769/1000000000000 : ℝ) (127303372573/250000000000 : ℝ) (509213490299/1000000000000 : ℝ) (512303560027/1000000000000 : ℝ) (256151780017/500000000000 : ℝ) (51229424073/100000000000 : ℝ) (256147120369/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 3 (512303560027/1000000000000 : ℝ) (256151780017/500000000000 : ℝ) (51229424073/100000000000 : ℝ) (256147120369/500000000000 : ℝ) (256149450189/500000000000 : ℝ) (256149450193/500000000000 : ℝ) (512298900357/1000000000000 : ℝ) (102459780073/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 4 (256149450189/500000000000 : ℝ) (256149450193/500000000000 : ℝ) (512298900357/1000000000000 : ℝ) (102459780073/200000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 5 (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 6 (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (301/2048 : ℝ))) 7 (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (301/2048 : ℝ)) hmem 8 (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (301/2048 : ℝ))) hcmem 8 (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (301/2048 : ℝ)) (495438585659/500000000000 : ℝ) (990877171321/1000000000000 : ℝ) (512298900367/1000000000000 : ℝ) (64037362547/125000000000 : ℝ) (812126118361/1000000000000 : ℝ) (406063059189/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1703_exp_lower
  have heNumeric : (2055774407803/1000000000000 : ℝ)/4 ≤ Real.exp (-332820871689/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055774407803/1000000000000 : ℝ)/4 ≤ Real.exp ((75/512 : ℝ)-(406063059189/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (75/512 : ℝ) (301/2048 : ℝ) (406063059189/500000000000 : ℝ) (2055774407803/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1704; no trusted numerical premise.
theorem cover8_leaf1704_exp_radius : (99769857519985271/100000000000000000 : ℝ) ≤ Real.exp ((-151/8192 : ℝ)/8) ∧ Real.exp ((-151/8192 : ℝ)/8) ≤ (997698575199852711/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-151/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1704_exp_lower : (184033488313462733/200000000000000000 : ℝ) ≤ Real.exp ((-332798495183/500000000000 : ℝ)/8) ∧ Real.exp ((-332798495183/500000000000 : ℝ)/8) ≤ (460083720783656833/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332798495183/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1704_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055866411959/1000000000000 : ℝ) ≤ 4*Real.exp (301/2048 : ℝ)*Real.exp (-mu (radius 8 (151/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055866411959/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (151/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1704_exp_radius
  have hrNumeric : (981736224511/1000000000000 : ℝ) ≤ Real.exp (-151/8192 : ℝ) ∧ Real.exp (-151/8192 : ℝ) ≤ (3834907127/3906250000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981736224511/1000000000000 : ℝ) ≤ (radius 8 (151/1024 : ℝ)) ∧ (radius 8 (151/1024 : ℝ)) ≤ (3834907127/3906250000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (151/1024 : ℝ)) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (151/1024 : ℝ)) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (151/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) (198173622451/200000000000 : ℝ) (7741157127/7812500000 : ℝ) (198165206281/200000000000 : ℝ) (990826031407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (151/1024 : ℝ)) 1 (198173622451/200000000000 : ℝ) (7741157127/7812500000 : ℝ) (198165206281/200000000000 : ℝ) (990826031407/1000000000000 : ℝ) (99084707183/100000000000 : ℝ) (123855883979/125000000000 : ℝ) (495423535803/500000000000 : ℝ) (990847071609/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (151/1024 : ℝ)) 2 (99084707183/100000000000 : ℝ) (123855883979/125000000000 : ℝ) (495423535803/500000000000 : ℝ) (990847071609/1000000000000 : ℝ) (495423535859/500000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (151/1024 : ℝ)) 3 (495423535859/500000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (151/1024 : ℝ)) 4 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (151/1024 : ℝ)) 5 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (151/1024 : ℝ)) 6 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (151/1024 : ℝ)) 7 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (151/1024 : ℝ))) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ) (595123584721/1000000000000 : ℝ) (148780896181/250000000000 : ℝ) (17446933/40000000 : ℝ) (27260832813/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 1 (595123584721/1000000000000 : ℝ) (148780896181/250000000000 : ℝ) (17446933/40000000 : ℝ) (27260832813/62500000000 : ℝ) (25782422743/50000000000 : ℝ) (257824227433/500000000000 : ℝ) (254743514507/500000000000 : ℝ) (509487029021/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 2 (25782422743/50000000000 : ℝ) (257824227433/500000000000 : ℝ) (254743514507/500000000000 : ℝ) (509487029021/1000000000000 : ℝ) (512567741937/1000000000000 : ℝ) (64070967743/125000000000 : ℝ) (512558483767/1000000000000 : ℝ) (20502339351/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 3 (512567741937/1000000000000 : ℝ) (64070967743/125000000000 : ℝ) (512558483767/1000000000000 : ℝ) (20502339351/40000000000 : ℝ) (128140778213/250000000000 : ℝ) (25628155643/50000000000 : ℝ) (512563112831/1000000000000 : ℝ) (512563112839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 4 (128140778213/250000000000 : ℝ) (25628155643/50000000000 : ℝ) (512563112831/1000000000000 : ℝ) (512563112839/1000000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 5 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 6 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (151/1024 : ℝ))) 7 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (151/1024 : ℝ)) hmem 8 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (151/1024 : ℝ))) hcmem 8 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (151/1024 : ℝ)) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (406284823299/500000000000 : ℝ) (101571205827/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1704_exp_lower
  have heNumeric : (2055866411959/1000000000000 : ℝ)/4 ≤ Real.exp (-332798495183/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055866411959/1000000000000 : ℝ)/4 ≤ Real.exp ((301/2048 : ℝ)-(101571205827/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (301/2048 : ℝ) (151/1024 : ℝ) (101571205827/125000000000 : ℝ) (2055866411959/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1705; no trusted numerical premise.
theorem cover8_leaf1705_exp_radius : (249420837910973147/250000000000000000 : ℝ) ≤ Real.exp ((-19/1024 : ℝ)/8) ∧ Real.exp ((-19/1024 : ℝ)/8) ≤ (997683351643892589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-19/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1705_exp_lower : (920121914063281921/1000000000000000000 : ℝ) ≤ Real.exp ((-332996409729/500000000000 : ℝ)/8) ∧ Real.exp ((-332996409729/500000000000 : ℝ)/8) ≤ (460060957031640961/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332996409729/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1705_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055052801259/1000000000000 : ℝ) ≤ 4*Real.exp (151/1024 : ℝ)*Real.exp (-mu (radius 8 (19/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2055052801259/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (19/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1705_exp_radius
  have hrNumeric : (981616390977/1000000000000 : ℝ) ≤ Real.exp (-19/1024 : ℝ) ∧ Real.exp (-19/1024 : ℝ) ≤ (490808195489/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981616390977/1000000000000 : ℝ) ≤ (radius 8 (19/128 : ℝ)) ∧ (radius 8 (19/128 : ℝ)) ≤ (490808195489/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (19/128 : ℝ)) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (19/128 : ℝ)) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (19/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) (30962756109/31250000000 : ℝ) (990808195489/1000000000000 : ℝ) (990765558029/1000000000000 : ℝ) (99076555803/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (19/128 : ℝ)) 1 (30962756109/31250000000 : ℝ) (990808195489/1000000000000 : ℝ) (990765558029/1000000000000 : ℝ) (99076555803/100000000000 : ℝ) (495393438379/500000000000 : ℝ) (24769671919/25000000000 : ℝ) (990786876529/1000000000000 : ℝ) (990786876531/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (19/128 : ℝ)) 2 (495393438379/500000000000 : ℝ) (24769671919/25000000000 : ℝ) (990786876529/1000000000000 : ℝ) (990786876531/1000000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (19/128 : ℝ)) 3 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (19/128 : ℝ)) 4 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (19/128 : ℝ)) 5 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (19/128 : ℝ)) 6 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (19/128 : ℝ)) 7 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (19/128 : ℝ))) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ) (595432254719/1000000000000 : ℝ) (297716127361/500000000000 : ℝ) (218440214611/500000000000 : ℝ) (43688042923/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 1 (595432254719/1000000000000 : ℝ) (297716127361/500000000000 : ℝ) (218440214611/500000000000 : ℝ) (43688042923/100000000000 : ℝ) (51615634197/100000000000 : ℝ) (64519542747/125000000000 : ℝ) (510032056849/1000000000000 : ℝ) (63754007107/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 2 (51615634197/100000000000 : ℝ) (64519542747/125000000000 : ℝ) (510032056849/1000000000000 : ℝ) (63754007107/125000000000 : ℝ) (513094199409/1000000000000 : ℝ) (64136774927/125000000000 : ℝ) (102617012381/200000000000 : ℝ) (513085061913/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 3 (513094199409/1000000000000 : ℝ) (64136774927/125000000000 : ℝ) (102617012381/200000000000 : ℝ) (513085061913/1000000000000 : ℝ) (513089630657/1000000000000 : ℝ) (102617926133/200000000000 : ℝ) (128272407659/250000000000 : ℝ) (102617926129/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 4 (513089630657/1000000000000 : ℝ) (102617926133/200000000000 : ℝ) (128272407659/250000000000 : ℝ) (102617926129/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 5 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 6 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (19/128 : ℝ))) 7 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (19/128 : ℝ)) hmem 8 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (19/128 : ℝ))) hcmem 8 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (19/128 : ℝ)) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (40672687847/50000000000 : ℝ) (406726878479/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1705_exp_lower
  have heNumeric : (2055052801259/1000000000000 : ℝ)/4 ≤ Real.exp (-332996409729/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055052801259/1000000000000 : ℝ)/4 ≤ Real.exp ((151/1024 : ℝ)-(406726878479/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (151/1024 : ℝ) (19/128 : ℝ) (406726878479/500000000000 : ℝ) (2055052801259/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1706; no trusted numerical premise.
theorem cover8_leaf1706_exp_radius : (249417032080055931/250000000000000000 : ℝ) ≤ Real.exp ((-153/8192 : ℝ)/8) ∧ Real.exp ((-153/8192 : ℝ)/8) ≤ (39906725132808949/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-153/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1706_exp_lower : (920132995012951667/1000000000000000000 : ℝ) ≤ Real.exp ((-665896476721/1000000000000 : ℝ)/8) ∧ Real.exp ((-665896476721/1000000000000 : ℝ)/8) ≤ (230033248753237917/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665896476721/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1706_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055250800209/1000000000000 : ℝ) ≤ 4*Real.exp (19/128 : ℝ)*Real.exp (-mu (radius 8 (153/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055250800209/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (153/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1706_exp_radius
  have hrNumeric : (981496572071/1000000000000 : ℝ) ≤ Real.exp (-153/8192 : ℝ) ∧ Real.exp (-153/8192 : ℝ) ≤ (122687071509/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981496572071/1000000000000 : ℝ) ≤ (radius 8 (153/1024 : ℝ)) ∧ (radius 8 (153/1024 : ℝ)) ≤ (122687071509/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (153/1024 : ℝ)) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (153/1024 : ℝ)) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (153/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) (198149657207/200000000000 : ℝ) (247687071509/250000000000 : ℝ) (123838136043/125000000000 : ℝ) (198141017669/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (153/1024 : ℝ)) 1 (198149657207/200000000000 : ℝ) (247687071509/250000000000 : ℝ) (123838136043/125000000000 : ℝ) (198141017669/200000000000 : ℝ) (990726687189/1000000000000 : ℝ) (990726687191/1000000000000 : ℝ) (495363343477/500000000000 : ℝ) (247681671739/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (153/1024 : ℝ)) 2 (990726687189/1000000000000 : ℝ) (990726687191/1000000000000 : ℝ) (495363343477/500000000000 : ℝ) (247681671739/250000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (153/1024 : ℝ)) 3 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (153/1024 : ℝ)) 4 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (153/1024 : ℝ)) 5 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (153/1024 : ℝ)) 6 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (153/1024 : ℝ)) 7 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (153/1024 : ℝ))) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ) (74467481821/125000000000 : ℝ) (595739854571/1000000000000 : ℝ) (109395986311/250000000000 : ℝ) (109395986313/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 1 (74467481821/125000000000 : ℝ) (595739854571/1000000000000 : ℝ) (109395986311/250000000000 : ℝ) (109395986313/250000000000 : ℝ) (258330949953/500000000000 : ℝ) (64582737489/125000000000 : ℝ) (510574378421/1000000000000 : ℝ) (127643594607/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 2 (258330949953/500000000000 : ℝ) (64582737489/125000000000 : ℝ) (510574378421/1000000000000 : ℝ) (127643594607/250000000000 : ℝ) (513618139163/1000000000000 : ℝ) (51361813917/100000000000 : ℝ) (128402280061/250000000000 : ℝ) (513609120251/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 3 (513618139163/1000000000000 : ℝ) (51361813917/100000000000 : ℝ) (128402280061/250000000000 : ℝ) (513609120251/1000000000000 : ℝ) (513613629703/1000000000000 : ℝ) (513613629711/1000000000000 : ℝ) (513613629683/1000000000000 : ℝ) (513613629691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 4 (513613629703/1000000000000 : ℝ) (513613629711/1000000000000 : ℝ) (513613629683/1000000000000 : ℝ) (513613629691/1000000000000 : ℝ) (513613629693/1000000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 5 (513613629693/1000000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 6 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (153/1024 : ℝ))) 7 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (153/1024 : ℝ)) hmem 8 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (153/1024 : ℝ))) hcmem 8 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (153/1024 : ℝ)) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (6361984193/7812500000 : ℝ) (814333976721/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1706_exp_lower
  have heNumeric : (2055250800209/1000000000000 : ℝ)/4 ≤ Real.exp (-665896476721/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055250800209/1000000000000 : ℝ)/4 ≤ Real.exp ((19/128 : ℝ)-(814333976721/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (19/128 : ℝ) (153/1024 : ℝ) (814333976721/1000000000000 : ℝ) (2055250800209/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1707; no trusted numerical premise.
theorem cover8_leaf1707_exp_radius : (249413226307210643/250000000000000000 : ℝ) ≤ Real.exp ((-77/4096 : ℝ)/8) ∧ Real.exp ((-77/4096 : ℝ)/8) ≤ (997652905228842573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-77/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1707_exp_lower : (460072259236000931/500000000000000000 : ℝ) ≤ Real.exp ((-4161226799/6250000000 : ℝ)/8) ∧ Real.exp ((-4161226799/6250000000 : ℝ)/8) ≤ (920144518472001863/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4161226799/6250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1707_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027728361901/500000000000 : ℝ) ≤ 4*Real.exp (153/1024 : ℝ)*Real.exp (-mu (radius 8 (77/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1027728361901/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (77/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1707_exp_radius
  have hrNumeric : (98137676779/100000000000 : ℝ) ≤ Real.exp (-77/4096 : ℝ) ∧ Real.exp (-77/4096 : ℝ) ≤ (981376767791/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98137676779/100000000000 : ℝ) ≤ (radius 8 (77/512 : ℝ)) ∧ (radius 8 (77/512 : ℝ)) ≤ (981376767791/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (77/512 : ℝ)) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (77/512 : ℝ)) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (77/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) (198137676779/200000000000 : ℝ) (123836047987/125000000000 : ℝ) (990644622349/1000000000000 : ℝ) (990644622351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (77/512 : ℝ)) 1 (198137676779/200000000000 : ℝ) (123836047987/125000000000 : ℝ) (990644622349/1000000000000 : ℝ) (990644622351/1000000000000 : ℝ) (495333251561/500000000000 : ℝ) (247666625781/250000000000 : ℝ) (6191665643/6250000000 : ℝ) (495333251441/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (77/512 : ℝ)) 2 (495333251561/500000000000 : ℝ) (247666625781/250000000000 : ℝ) (6191665643/6250000000 : ℝ) (495333251441/500000000000 : ℝ) (990666503001/1000000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (77/512 : ℝ)) 3 (990666503001/1000000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (77/512 : ℝ)) 4 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (77/512 : ℝ)) 5 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (77/512 : ℝ)) 6 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (77/512 : ℝ)) 7 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (77/512 : ℝ))) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ) (59604639457/100000000000 : ℝ) (298023197287/500000000000 : ℝ) (438283913851/1000000000000 : ℝ) (438283913859/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 1 (59604639457/100000000000 : ℝ) (298023197287/500000000000 : ℝ) (438283913851/1000000000000 : ℝ) (438283913859/1000000000000 : ℝ) (51716515421/100000000000 : ℝ) (517165154217/1000000000000 : ℝ) (102222805019/200000000000 : ℝ) (255557012551/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 2 (51716515421/100000000000 : ℝ) (517165154217/1000000000000 : ℝ) (102222805019/200000000000 : ℝ) (255557012551/500000000000 : ℝ) (128534897413/250000000000 : ℝ) (25706979483/50000000000 : ℝ) (128532671821/250000000000 : ℝ) (128532671823/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 3 (128534897413/250000000000 : ℝ) (25706979483/50000000000 : ℝ) (128532671821/250000000000 : ℝ) (128532671823/250000000000 : ℝ) (128533784617/250000000000 : ℝ) (128533784619/250000000000 : ℝ) (32133446153/62500000000 : ℝ) (514135138457/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 4 (128533784617/250000000000 : ℝ) (128533784619/250000000000 : ℝ) (32133446153/62500000000 : ℝ) (514135138457/1000000000000 : ℝ) (257067569229/500000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 5 (257067569229/500000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 6 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (77/512 : ℝ))) 7 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (77/512 : ℝ)) hmem 8 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (77/512 : ℝ))) hcmem 8 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (77/512 : ℝ)) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (815210350321/1000000000000 : ℝ) (40760517517/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1707_exp_lower
  have heNumeric : (1027728361901/500000000000 : ℝ)/4 ≤ Real.exp (-4161226799/6250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027728361901/500000000000 : ℝ)/4 ≤ Real.exp ((153/1024 : ℝ)-(40760517517/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (153/1024 : ℝ) (77/512 : ℝ) (40760517517/50000000000 : ℝ) (1027728361901/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1708; no trusted numerical premise.
theorem cover8_leaf1708_exp_radius : (249409420592436397/250000000000000000 : ℝ) ≤ Real.exp ((-155/8192 : ℝ)/8) ∧ Real.exp ((-155/8192 : ℝ)/8) ≤ (997637682369745589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-155/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1708_exp_lower : (460078239720238263/500000000000000000 : ℝ) ≤ Real.exp ((-66569229643/100000000000 : ℝ)/8) ∧ Real.exp ((-66569229643/100000000000 : ℝ)/8) ≤ (920156479440476527/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66569229643/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1708_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055670484759/1000000000000 : ℝ) ≤ 4*Real.exp (77/512 : ℝ)*Real.exp (-mu (radius 8 (155/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055670484759/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (155/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1708_exp_radius
  have hrNumeric : (981256978133/1000000000000 : ℝ) ≤ Real.exp (-155/8192 : ℝ) ∧ Real.exp (-155/8192 : ℝ) ≤ (490628489067/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981256978133/1000000000000 : ℝ) ≤ (radius 8 (155/1024 : ℝ)) ∧ (radius 8 (155/1024 : ℝ)) ≤ (490628489067/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (155/1024 : ℝ)) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (155/1024 : ℝ)) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (155/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) (495314244533/500000000000 : ℝ) (990628489067/1000000000000 : ℝ) (198116832009/200000000000 : ℝ) (495292080023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (155/1024 : ℝ)) 1 (495314244533/500000000000 : ℝ) (990628489067/1000000000000 : ℝ) (198116832009/200000000000 : ℝ) (495292080023/500000000000 : ℝ) (198121264911/200000000000 : ℝ) (990606324557/1000000000000 : ℝ) (990606324307/1000000000000 : ℝ) (990606324309/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (155/1024 : ℝ)) 2 (198121264911/200000000000 : ℝ) (990606324557/1000000000000 : ℝ) (990606324307/1000000000000 : ℝ) (990606324309/1000000000000 : ℝ) (990606324431/1000000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (155/1024 : ℝ)) 3 (990606324431/1000000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (155/1024 : ℝ)) 4 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (155/1024 : ℝ)) 5 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (155/1024 : ℝ)) 6 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (155/1024 : ℝ)) 7 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (155/1024 : ℝ))) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ) (298175942429/500000000000 : ℝ) (298175942431/500000000000 : ℝ) (438980375093/1000000000000 : ℝ) (438980375101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 1 (298175942429/500000000000 : ℝ) (298175942431/500000000000 : ℝ) (438980375093/1000000000000 : ℝ) (438980375101/1000000000000 : ℝ) (20706645199/40000000000 : ℝ) (258833064991/500000000000 : ℝ) (63956378457/125000000000 : ℝ) (31978189229/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 2 (20706645199/40000000000 : ℝ) (258833064991/500000000000 : ℝ) (63956378457/125000000000 : ℝ) (31978189229/62500000000 : ℝ) (102931715763/200000000000 : ℝ) (514658578823/1000000000000 : ℝ) (514649791007/1000000000000 : ℝ) (64331223877/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 3 (102931715763/200000000000 : ℝ) (514658578823/1000000000000 : ℝ) (514649791007/1000000000000 : ℝ) (64331223877/125000000000 : ℝ) (514654184911/1000000000000 : ℝ) (12866354623/25000000000 : ℝ) (128663546223/250000000000 : ℝ) (514654184901/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 4 (514654184911/1000000000000 : ℝ) (12866354623/25000000000 : ℝ) (128663546223/250000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 5 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 6 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (155/1024 : ℝ))) 7 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (155/1024 : ℝ)) hmem 8 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (155/1024 : ℝ))) hcmem 8 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (155/1024 : ℝ)) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (816082921411/1000000000000 : ℝ) (81608292143/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1708_exp_lower
  have heNumeric : (2055670484759/1000000000000 : ℝ)/4 ≤ Real.exp (-66569229643/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055670484759/1000000000000 : ℝ)/4 ≤ Real.exp ((77/512 : ℝ)-(81608292143/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (77/512 : ℝ) (155/1024 : ℝ) (81608292143/100000000000 : ℝ) (2055670484759/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1709; no trusted numerical premise.
theorem cover8_leaf1709_exp_radius : (249405614935732307/250000000000000000 : ℝ) ≤ Real.exp ((-39/2048 : ℝ)/8) ∧ Real.exp ((-39/2048 : ℝ)/8) ≤ (997622459742929229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-39/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1709_exp_lower : (36806754920206743/40000000000000000 : ℝ) ≤ Real.exp ((-133116909071/200000000000 : ℝ)/8) ∧ Real.exp ((-133116909071/200000000000 : ℝ)/8) ≤ (14377638640705759/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133116909071/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1709_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027945998699/500000000000 : ℝ) ≤ 4*Real.exp (155/1024 : ℝ)*Real.exp (-mu (radius 8 (39/256 : ℝ))) ∧ (20549/10000 : ℝ) < (1027945998699/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (39/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1709_exp_radius
  have hrNumeric : (981137203097/1000000000000 : ℝ) ≤ Real.exp (-39/2048 : ℝ) ∧ Real.exp (-39/2048 : ℝ) ≤ (490568601549/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981137203097/1000000000000 : ℝ) ≤ (radius 8 (39/256 : ℝ)) ∧ (radius 8 (39/256 : ℝ)) ≤ (490568601549/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (39/256 : ℝ)) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (39/256 : ℝ)) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (39/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) (247642150387/250000000000 : ℝ) (990568601549/1000000000000 : ℝ) (990523701431/1000000000000 : ℝ) (123815462679/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (39/256 : ℝ)) 1 (247642150387/250000000000 : ℝ) (990568601549/1000000000000 : ℝ) (990523701431/1000000000000 : ℝ) (123815462679/125000000000 : ℝ) (990546151489/1000000000000 : ℝ) (990546151491/1000000000000 : ℝ) (198109230247/200000000000 : ℝ) (990546151237/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (39/256 : ℝ)) 2 (990546151489/1000000000000 : ℝ) (990546151491/1000000000000 : ℝ) (198109230247/200000000000 : ℝ) (990546151237/1000000000000 : ℝ) (495273075681/500000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (39/256 : ℝ)) 3 (495273075681/500000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (39/256 : ℝ)) 4 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (39/256 : ℝ)) 5 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (39/256 : ℝ)) 6 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (39/256 : ℝ)) 7 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (39/256 : ℝ))) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ) (298328167703/500000000000 : ℝ) (59665633541/100000000000 : ℝ) (439673368323/1000000000000 : ℝ) (439673368331/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 1 (298328167703/500000000000 : ℝ) (59665633541/100000000000 : ℝ) (439673368323/1000000000000 : ℝ) (439673368331/1000000000000 : ℝ) (64770606483/125000000000 : ℝ) (518164851871/1000000000000 : ℝ) (512185416347/1000000000000 : ℝ) (102437083271/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 2 (64770606483/125000000000 : ℝ) (518164851871/1000000000000 : ℝ) (512185416347/1000000000000 : ℝ) (102437083271/200000000000 : ℝ) (103035026821/200000000000 : ℝ) (515175134113/1000000000000 : ℝ) (16098951841/31250000000 : ℝ) (12879161473/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 3 (103035026821/200000000000 : ℝ) (515175134113/1000000000000 : ℝ) (16098951841/31250000000 : ℝ) (12879161473/25000000000 : ℝ) (128792699127/250000000000 : ℝ) (515170796517/1000000000000 : ℝ) (51517079649/100000000000 : ℝ) (515170796499/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 4 (128792699127/250000000000 : ℝ) (515170796517/1000000000000 : ℝ) (51517079649/100000000000 : ℝ) (515170796499/1000000000000 : ℝ) (515170796499/1000000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 5 (515170796499/1000000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 6 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (39/256 : ℝ))) 7 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (39/256 : ℝ)) hmem 8 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (39/256 : ℝ))) hcmem 8 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (39/256 : ℝ)) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (204237933209/250000000000 : ℝ) (163390346571/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1709_exp_lower
  have heNumeric : (1027945998699/500000000000 : ℝ)/4 ≤ Real.exp (-133116909071/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027945998699/500000000000 : ℝ)/4 ≤ Real.exp ((155/1024 : ℝ)-(163390346571/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (155/1024 : ℝ) (39/256 : ℝ) (163390346571/200000000000 : ℝ) (1027945998699/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1710; no trusted numerical premise.
theorem cover8_leaf1710_exp_radius : (997607237348389947/1000000000000000000 : ℝ) ≤ Real.exp ((-157/8192 : ℝ)/8) ∧ Real.exp ((-157/8192 : ℝ)/8) ≤ (249401809337097487/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-157/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1710_exp_lower : (230045423585763209/250000000000000000 : ℝ) ≤ Real.exp ((-332736538349/500000000000 : ℝ)/8) ∧ Real.exp ((-332736538349/500000000000 : ℝ)/8) ≤ (920181694343052837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332736538349/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1710_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056121177691/1000000000000 : ℝ) ≤ 4*Real.exp (39/256 : ℝ)*Real.exp (-mu (radius 8 (157/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2056121177691/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (157/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1710_exp_radius
  have hrNumeric : (490508721341/500000000000 : ℝ) ≤ Real.exp (-157/8192 : ℝ) ∧ Real.exp (-157/8192 : ℝ) ≤ (981017442683/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490508721341/500000000000 : ℝ) ≤ (radius 8 (157/1024 : ℝ)) ∧ (radius 8 (157/1024 : ℝ)) ≤ (981017442683/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (157/1024 : ℝ)) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (157/1024 : ℝ)) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (157/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) (990508721341/1000000000000 : ℝ) (495254360671/500000000000 : ℝ) (990463246507/1000000000000 : ℝ) (247615811627/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (157/1024 : ℝ)) 1 (990508721341/1000000000000 : ℝ) (495254360671/500000000000 : ℝ) (990463246507/1000000000000 : ℝ) (247615811627/250000000000 : ℝ) (247621495981/250000000000 : ℝ) (39619439357/40000000000 : ℝ) (990485983663/1000000000000 : ℝ) (198097196733/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (157/1024 : ℝ)) 2 (247621495981/250000000000 : ℝ) (39619439357/40000000000 : ℝ) (990485983663/1000000000000 : ℝ) (198097196733/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (157/1024 : ℝ)) 3 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (157/1024 : ℝ)) 4 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (157/1024 : ℝ)) 5 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (157/1024 : ℝ)) 6 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (157/1024 : ℝ)) 7 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (157/1024 : ℝ))) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ) (298479878011/500000000000 : ℝ) (23878390241/40000000000 : ℝ) (220181466093/500000000000 : ℝ) (220181466097/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 1 (298479878011/500000000000 : ℝ) (23878390241/40000000000 : ℝ) (220181466093/500000000000 : ℝ) (220181466097/500000000000 : ℝ) (64832668013/125000000000 : ℝ) (51866134411/100000000000 : ℝ) (128179305213/250000000000 : ℝ) (512717220859/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 2 (64832668013/125000000000 : ℝ) (51866134411/100000000000 : ℝ) (128179305213/250000000000 : ℝ) (512717220859/1000000000000 : ℝ) (257844641239/500000000000 : ℝ) (103137856497/200000000000 : ℝ) (103136143599/200000000000 : ℝ) (515680718003/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 3 (257844641239/500000000000 : ℝ) (103137856497/200000000000 : ℝ) (103136143599/200000000000 : ℝ) (515680718003/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (128921250061/250000000000 : ℝ) (257842500109/500000000000 : ℝ) (515685000227/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 4 (128921250059/250000000000 : ℝ) (128921250061/250000000000 : ℝ) (257842500109/500000000000 : ℝ) (515685000227/1000000000000 : ℝ) (515685000227/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 5 (515685000227/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 6 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (157/1024 : ℝ))) 7 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (157/1024 : ℝ)) hmem 8 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (157/1024 : ℝ))) hcmem 8 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (157/1024 : ℝ)) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (817816826679/1000000000000 : ℝ) (408908413349/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1710_exp_lower
  have heNumeric : (2056121177691/1000000000000 : ℝ)/4 ≤ Real.exp (-332736538349/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056121177691/1000000000000 : ℝ)/4 ≤ Real.exp ((39/256 : ℝ)-(408908413349/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (39/256 : ℝ) (157/1024 : ℝ) (408908413349/500000000000 : ℝ) (2056121177691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1711; no trusted numerical premise.
theorem cover8_leaf1711_exp_radius : (997592015186124201/1000000000000000000 : ℝ) ≤ Real.exp ((-79/4096 : ℝ)/8) ∧ Real.exp ((-79/4096 : ℝ)/8) ≤ (498796007593062101/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-79/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1711_exp_lower : (920194938713907951/1000000000000000000 : ℝ) ≤ Real.exp ((-26614317273/40000000000 : ℝ)/8) ∧ Real.exp ((-26614317273/40000000000 : ℝ)/8) ≤ (57512183669619247/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-26614317273/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1711_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028178971567/500000000000 : ℝ) ≤ 4*Real.exp (157/1024 : ℝ)*Real.exp (-mu (radius 8 (79/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1028178971567/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (79/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1711_exp_radius
  have hrNumeric : (196179539377/200000000000 : ℝ) ≤ Real.exp (-79/4096 : ℝ) ∧ Real.exp (-79/4096 : ℝ) ≤ (490448848443/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196179539377/200000000000 : ℝ) ≤ (radius 8 (79/512 : ℝ)) ∧ (radius 8 (79/512 : ℝ)) ≤ (490448848443/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (79/512 : ℝ)) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (79/512 : ℝ)) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (79/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) (495224424221/500000000000 : ℝ) (990448848443/1000000000000 : ℝ) (990402795273/1000000000000 : ℝ) (495201397637/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (79/512 : ℝ)) 1 (495224424221/500000000000 : ℝ) (990448848443/1000000000000 : ℝ) (990402795273/1000000000000 : ℝ) (495201397637/500000000000 : ℝ) (990425821857/1000000000000 : ℝ) (990425821859/1000000000000 : ℝ) (990425821589/1000000000000 : ℝ) (990425821591/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (79/512 : ℝ)) 2 (990425821857/1000000000000 : ℝ) (990425821859/1000000000000 : ℝ) (990425821589/1000000000000 : ℝ) (990425821591/1000000000000 : ℝ) (990425821723/1000000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (79/512 : ℝ)) 3 (990425821723/1000000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (79/512 : ℝ)) 4 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (79/512 : ℝ)) 5 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (79/512 : ℝ)) 6 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (79/512 : ℝ)) 7 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (79/512 : ℝ))) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ) (119452431273/200000000000 : ℝ) (597262156369/1000000000000 : ℝ) (44104910467/100000000000 : ℝ) (220524552339/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 1 (119452431273/200000000000 : ℝ) (597262156369/1000000000000 : ℝ) (44104910467/100000000000 : ℝ) (220524552339/500000000000 : ℝ) (519155630517/1000000000000 : ℝ) (129788907631/250000000000 : ℝ) (513246470341/1000000000000 : ℝ) (128311617587/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 2 (519155630517/1000000000000 : ℝ) (129788907631/250000000000 : ℝ) (513246470341/1000000000000 : ℝ) (128311617587/250000000000 : ℝ) (516201050429/1000000000000 : ℝ) (129050262609/250000000000 : ℝ) (258096297397/500000000000 : ℝ) (258096297401/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 3 (516201050429/1000000000000 : ℝ) (129050262609/250000000000 : ℝ) (258096297397/500000000000 : ℝ) (258096297401/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (516196822619/1000000000000 : ℝ) (258098411297/500000000000 : ℝ) (258098411301/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 4 (516196822611/1000000000000 : ℝ) (516196822619/1000000000000 : ℝ) (258098411297/500000000000 : ℝ) (258098411301/500000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 5 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 6 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (79/512 : ℝ))) 7 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (79/512 : ℝ)) hmem 8 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (79/512 : ℝ))) hcmem 8 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (79/512 : ℝ)) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (818678244307/1000000000000 : ℝ) (32747129773/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1711_exp_lower
  have heNumeric : (1028178971567/500000000000 : ℝ)/4 ≤ Real.exp (-26614317273/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028178971567/500000000000 : ℝ)/4 ≤ Real.exp ((157/1024 : ℝ)-(32747129773/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (157/1024 : ℝ) (79/512 : ℝ) (32747129773/40000000000 : ℝ) (1028178971567/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1712; no trusted numerical premise.
theorem cover8_leaf1712_exp_radius : (997576793256128447/1000000000000000000 : ℝ) ≤ Real.exp ((-159/8192 : ℝ)/8) ∧ Real.exp ((-159/8192 : ℝ)/8) ≤ (15587137394627007/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-159/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1712_exp_lower : (46010430073141537/50000000000000000 : ℝ) ≤ Real.exp ((-665239151363/1000000000000 : ℝ)/8) ∧ Real.exp ((-665239151363/1000000000000 : ℝ)/8) ≤ (920208601462830741/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665239151363/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1712_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056602212787/1000000000000 : ℝ) ≤ 4*Real.exp (79/512 : ℝ)*Real.exp (-mu (radius 8 (159/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2056602212787/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (159/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1712_exp_radius
  have hrNumeric : (196155593141/200000000000 : ℝ) ≤ Real.exp (-159/8192 : ℝ) ∧ Real.exp (-159/8192 : ℝ) ≤ (490388982853/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196155593141/200000000000 : ℝ) ≤ (radius 8 (159/1024 : ℝ)) ∧ (radius 8 (159/1024 : ℝ)) ≤ (490388982853/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (159/1024 : ℝ)) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (159/1024 : ℝ)) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (159/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) (247597245713/250000000000 : ℝ) (990388982853/1000000000000 : ℝ) (61896396733/62500000000 : ℝ) (99034234773/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (159/1024 : ℝ)) 1 (247597245713/250000000000 : ℝ) (990388982853/1000000000000 : ℝ) (61896396733/62500000000 : ℝ) (99034234773/100000000000 : ℝ) (99036566529/100000000000 : ℝ) (247591416323/250000000000 : ℝ) (198073133003/200000000000 : ℝ) (495182832509/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (159/1024 : ℝ)) 2 (99036566529/100000000000 : ℝ) (247591416323/250000000000 : ℝ) (198073133003/200000000000 : ℝ) (495182832509/500000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (159/1024 : ℝ)) 3 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (159/1024 : ℝ)) 4 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (159/1024 : ℝ)) 5 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (159/1024 : ℝ)) 6 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (159/1024 : ℝ)) 7 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (159/1024 : ℝ))) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ) (29878177297/50000000000 : ℝ) (597563545943/1000000000000 : ℝ) (441731923093/1000000000000 : ℝ) (441731923101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 1 (29878177297/50000000000 : ℝ) (597563545943/1000000000000 : ℝ) (441731923093/1000000000000 : ℝ) (441731923101/1000000000000 : ℝ) (129911933629/250000000000 : ℝ) (259823867261/500000000000 : ℝ) (25688659673/50000000000 : ℝ) (513773193467/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 2 (129911933629/250000000000 : ℝ) (259823867261/500000000000 : ℝ) (25688659673/50000000000 : ℝ) (513773193467/1000000000000 : ℝ) (129177615997/250000000000 : ℝ) (103342092799/200000000000 : ℝ) (258351057689/500000000000 : ℝ) (103340423077/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 3 (129177615997/250000000000 : ℝ) (103342092799/200000000000 : ℝ) (258351057689/500000000000 : ℝ) (103340423077/200000000000 : ℝ) (516706289683/1000000000000 : ℝ) (51670628969/100000000000 : ℝ) (258353144833/500000000000 : ℝ) (258353144837/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 4 (516706289683/1000000000000 : ℝ) (51670628969/100000000000 : ℝ) (258353144833/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 5 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 6 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (159/1024 : ℝ))) 7 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (159/1024 : ℝ)) hmem 8 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (159/1024 : ℝ))) hcmem 8 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (159/1024 : ℝ)) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (819536026347/1000000000000 : ℝ) (819536026363/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1712_exp_lower
  have heNumeric : (2056602212787/1000000000000 : ℝ)/4 ≤ Real.exp (-665239151363/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056602212787/1000000000000 : ℝ)/4 ≤ Real.exp ((79/512 : ℝ)-(819536026363/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (79/512 : ℝ) (159/1024 : ℝ) (819536026363/1000000000000 : ℝ) (2056602212787/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1713; no trusted numerical premise.
theorem cover8_leaf1713_exp_radius : (997561571558399139/1000000000000000000 : ℝ) ≤ Real.exp ((-5/256 : ℝ)/8) ∧ Real.exp ((-5/256 : ℝ)/8) ≤ (49878078577919957/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1713_exp_lower : (92022267801412451/100000000000000000 : ℝ) ≤ Real.exp ((-665116775253/1000000000000 : ℝ)/8) ∧ Real.exp ((-665116775253/1000000000000 : ℝ)/8) ≤ (920222678014124511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665116775253/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1713_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028426953583/500000000000 : ℝ) ≤ 4*Real.exp (159/1024 : ℝ)*Real.exp (-mu (radius 8 (5/32 : ℝ))) ∧ (20549/10000 : ℝ) < (1028426953583/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (5/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1713_exp_radius
  have hrNumeric : (980658249139/1000000000000 : ℝ) ≤ Real.exp (-5/256 : ℝ) ∧ Real.exp (-5/256 : ℝ) ≤ (49032912457/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980658249139/1000000000000 : ℝ) ≤ (radius 8 (5/32 : ℝ)) ∧ (radius 8 (5/32 : ℝ)) ≤ (49032912457/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (5/32 : ℝ)) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (5/32 : ℝ)) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (5/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) (990329124569/1000000000000 : ℝ) (99032912457/100000000000 : ℝ) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (5/32 : ℝ)) 1 (990329124569/1000000000000 : ℝ) (99032912457/100000000000 : ℝ) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ) (990305514221/1000000000000 : ℝ) (495152757111/500000000000 : ℝ) (990305513939/1000000000000 : ℝ) (990305513941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (5/32 : ℝ)) 2 (990305514221/1000000000000 : ℝ) (495152757111/500000000000 : ℝ) (990305513939/1000000000000 : ℝ) (990305513941/1000000000000 : ℝ) (6189409463/6250000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (5/32 : ℝ)) 3 (6189409463/6250000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (5/32 : ℝ)) 4 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (5/32 : ℝ)) 5 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (5/32 : ℝ)) 6 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (5/32 : ℝ)) 7 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (5/32 : ℝ))) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ) (74732991763/125000000000 : ℝ) (149465983527/250000000000 : ℝ) (442411424139/1000000000000 : ℝ) (442411424147/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 1 (74732991763/125000000000 : ℝ) (149465983527/250000000000 : ℝ) (442411424139/1000000000000 : ℝ) (442411424147/1000000000000 : ℝ) (520137679121/1000000000000 : ℝ) (65017209891/125000000000 : ℝ) (128574354589/250000000000 : ℝ) (128574354591/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 2 (520137679121/1000000000000 : ℝ) (65017209891/125000000000 : ℝ) (128574354589/250000000000 : ℝ) (128574354591/250000000000 : ℝ) (258608774369/500000000000 : ℝ) (258608774373/500000000000 : ℝ) (51720930537/100000000000 : ℝ) (258604652689/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 3 (258608774369/500000000000 : ℝ) (258608774373/500000000000 : ℝ) (51720930537/100000000000 : ℝ) (258604652689/500000000000 : ℝ) (258606713527/500000000000 : ℝ) (258606713531/500000000000 : ℝ) (517213427037/1000000000000 : ℝ) (258606713523/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 4 (258606713527/500000000000 : ℝ) (258606713531/500000000000 : ℝ) (517213427037/1000000000000 : ℝ) (258606713523/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 5 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 6 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (5/32 : ℝ))) 7 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (5/32 : ℝ)) hmem 8 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (5/32 : ℝ))) hcmem 8 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (5/32 : ℝ)) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (164078042547/200000000000 : ℝ) (820390212753/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1713_exp_lower
  have heNumeric : (1028426953583/500000000000 : ℝ)/4 ≤ Real.exp (-665116775253/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028426953583/500000000000 : ℝ)/4 ≤ Real.exp ((159/1024 : ℝ)-(820390212753/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (159/1024 : ℝ) (5/32 : ℝ) (820390212753/1000000000000 : ℝ) (1028426953583/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1714; no trusted numerical premise.
theorem cover8_leaf1714_exp_radius : (124691391107465711/125000000000000000 : ℝ) ≤ Real.exp ((-81/4096 : ℝ)/8) ∧ Real.exp ((-81/4096 : ℝ)/8) ≤ (997531128859725689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-81/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1714_exp_lower : (460069863012122759/500000000000000000 : ℝ) ≤ Real.exp ((-332918977431/500000000000 : ℝ)/8) ∧ Real.exp ((-332918977431/500000000000 : ℝ)/8) ≤ (920139726024245519/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332918977431/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1714_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027685540413/500000000000 : ℝ) ≤ 4*Real.exp (5/32 : ℝ)*Real.exp (-mu (radius 8 (81/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1027685540413/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (81/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1714_exp_radius
  have hrNumeric : (196083771969/200000000000 : ℝ) ≤ Real.exp (-81/4096 : ℝ) ∧ Real.exp (-81/4096 : ℝ) ≤ (490209429923/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196083771969/200000000000 : ℝ) ≤ (radius 8 (81/512 : ℝ)) ∧ (radius 8 (81/512 : ℝ)) ≤ (490209429923/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (81/512 : ℝ)) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (81/512 : ℝ)) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (81/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196083771969/200000000000 : ℝ) (490209429923/500000000000 : ℝ) (495104714961/500000000000 : ℝ) (990209429923/1000000000000 : ℝ) (990161027229/1000000000000 : ℝ) (990161027231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (81/512 : ℝ)) 1 (495104714961/500000000000 : ℝ) (990209429923/1000000000000 : ℝ) (990161027229/1000000000000 : ℝ) (990161027231/1000000000000 : ℝ) (39607409143/40000000000 : ℝ) (990185228577/1000000000000 : ℝ) (990185228279/1000000000000 : ℝ) (495092614141/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (81/512 : ℝ)) 2 (39607409143/40000000000 : ℝ) (990185228577/1000000000000 : ℝ) (990185228279/1000000000000 : ℝ) (495092614141/500000000000 : ℝ) (990185228427/1000000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (81/512 : ℝ)) 3 (990185228427/1000000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (81/512 : ℝ)) 4 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (81/512 : ℝ)) 5 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (81/512 : ℝ)) 6 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (81/512 : ℝ)) 7 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (81/512 : ℝ))) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49230871449/250000000000 : ℝ) (98461742901/500000000000 : ℝ) (299230871449/500000000000 : ℝ) (598461742901/1000000000000 : ℝ) (443760617671/1000000000000 : ℝ) (443760617679/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 1 (299230871449/500000000000 : ℝ) (598461742901/1000000000000 : ℝ) (443760617671/1000000000000 : ℝ) (443760617679/1000000000000 : ℝ) (130277795071/250000000000 : ℝ) (52111118029/100000000000 : ℝ) (515338483601/1000000000000 : ℝ) (64417310451/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 2 (130277795071/250000000000 : ℝ) (52111118029/100000000000 : ℝ) (515338483601/1000000000000 : ℝ) (64417310451/125000000000 : ℝ) (259112415971/500000000000 : ℝ) (518224831949/1000000000000 : ℝ) (2024284351/3906250000 : ℝ) (64777099233/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 3 (259112415971/500000000000 : ℝ) (518224831949/1000000000000 : ℝ) (2024284351/3906250000 : ℝ) (64777099233/125000000000 : ℝ) (518220812899/1000000000000 : ℝ) (518220812907/1000000000000 : ℝ) (518220812883/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 4 (518220812899/1000000000000 : ℝ) (518220812907/1000000000000 : ℝ) (518220812883/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ) (518220812891/1000000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 5 (518220812891/1000000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 6 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (81/512 : ℝ))) 7 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (81/512 : ℝ)) hmem 8 (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (81/512 : ℝ))) hcmem 8 (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (81/512 : ℝ)) (495092614213/500000000000 : ℝ) (99018522843/100000000000 : ℝ) (51822081289/100000000000 : ℝ) (518220812899/1000000000000 : ℝ) (822087954843/1000000000000 : ℝ) (411043977431/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1714_exp_lower
  have heNumeric : (1027685540413/500000000000 : ℝ)/4 ≤ Real.exp (-332918977431/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027685540413/500000000000 : ℝ)/4 ≤ Real.exp ((5/32 : ℝ)-(411043977431/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (5/32 : ℝ) (81/512 : ℝ) (411043977431/500000000000 : ℝ) (1027685540413/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1715; no trusted numerical premise.
theorem cover8_leaf1715_exp_radius : (124687585886259437/125000000000000000 : ℝ) ≤ Real.exp ((-41/2048 : ℝ)/8) ∧ Real.exp ((-41/2048 : ℝ)/8) ≤ (997500687090075497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1715_exp_lower : (230042675280186791/250000000000000000 : ℝ) ≤ Real.exp ((-665568651631/1000000000000 : ℝ)/8) ∧ Real.exp ((-665568651631/1000000000000 : ℝ)/8) ≤ (184034140224149433/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665568651631/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1715_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027962336719/500000000000 : ℝ) ≤ 4*Real.exp (81/512 : ℝ)*Real.exp (-mu (radius 8 (41/256 : ℝ))) ∧ (20549/10000 : ℝ) < (1027962336719/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (41/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1715_exp_radius
  have hrNumeric : (245044882247/250000000000 : ℝ) ≤ Real.exp (-41/2048 : ℝ) ∧ Real.exp (-41/2048 : ℝ) ≤ (980179528989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245044882247/250000000000 : ℝ) ≤ (radius 8 (41/256 : ℝ)) ∧ (radius 8 (41/256 : ℝ)) ≤ (980179528989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (41/256 : ℝ)) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (41/256 : ℝ)) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (41/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) (495044882247/500000000000 : ℝ) (198017952899/200000000000 : ℝ) (49502008267/50000000000 : ℝ) (495020082671/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (41/256 : ℝ)) 1 (495044882247/500000000000 : ℝ) (198017952899/200000000000 : ℝ) (49502008267/50000000000 : ℝ) (495020082671/500000000000 : ℝ) (990064964917/1000000000000 : ℝ) (990064964919/1000000000000 : ℝ) (495032482303/500000000000 : ℝ) (966860317/976562500 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (41/256 : ℝ)) 2 (990064964917/1000000000000 : ℝ) (990064964919/1000000000000 : ℝ) (495032482303/500000000000 : ℝ) (966860317/976562500 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (41/256 : ℝ)) 3 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (41/256 : ℝ)) 4 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (41/256 : ℝ)) 5 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (41/256 : ℝ)) 6 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (41/256 : ℝ)) 7 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (41/256 : ℝ))) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ) (149763913687/250000000000 : ℝ) (18720489211/31250000000 : ℝ) (222548483199/500000000000 : ℝ) (222548483203/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 1 (149763913687/250000000000 : ℝ) (18720489211/31250000000 : ℝ) (222548483199/500000000000 : ℝ) (222548483203/500000000000 : ℝ) (522076310573/1000000000000 : ℝ) (522076310579/1000000000000 : ℝ) (64546235201/125000000000 : ℝ) (103273976323/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 2 (522076310573/1000000000000 : ℝ) (522076310579/1000000000000 : ℝ) (64546235201/125000000000 : ℝ) (103273976323/200000000000 : ℝ) (51922309609/100000000000 : ℝ) (519223096097/1000000000000 : ℝ) (259607628297/500000000000 : ℝ) (259607628301/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 3 (51922309609/100000000000 : ℝ) (519223096097/1000000000000 : ℝ) (259607628297/500000000000 : ℝ) (259607628301/500000000000 : ℝ) (259609588171/500000000000 : ℝ) (10384383527/20000000000 : ℝ) (519219176327/1000000000000 : ℝ) (103843835267/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 4 (259609588171/500000000000 : ℝ) (10384383527/20000000000 : ℝ) (519219176327/1000000000000 : ℝ) (103843835267/200000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 5 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 6 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (41/256 : ℝ))) 7 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (41/256 : ℝ)) hmem 8 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (41/256 : ℝ))) hcmem 8 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (41/256 : ℝ)) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (411885888307/500000000000 : ℝ) (823771776631/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1715_exp_lower
  have heNumeric : (1027962336719/500000000000 : ℝ)/4 ≤ Real.exp (-665568651631/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027962336719/500000000000 : ℝ)/4 ≤ Real.exp ((81/512 : ℝ)-(823771776631/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (81/512 : ℝ) (41/256 : ℝ) (823771776631/1000000000000 : ℝ) (1027962336719/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1716; no trusted numerical premise.
theorem cover8_leaf1716_exp_radius : (997470246249420213/1000000000000000000 : ℝ) ≤ Real.exp ((-83/4096 : ℝ)/8) ∧ Real.exp ((-83/4096 : ℝ)/8) ≤ (498735123124710107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1716_exp_lower : (920203244436774723/1000000000000000000 : ℝ) ≤ Real.exp ((-332642861887/500000000000 : ℝ)/8) ∧ Real.exp ((-332642861887/500000000000 : ℝ)/8) ≤ (230050811109193681/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332642861887/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1716_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028253217047/500000000000 : ℝ) ≤ 4*Real.exp (41/256 : ℝ)*Real.exp (-mu (radius 8 (83/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1028253217047/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (83/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1716_exp_radius
  have hrNumeric : (489970128277/500000000000 : ℝ) ≤ Real.exp (-83/4096 : ℝ) ∧ Real.exp (-83/4096 : ℝ) ≤ (195988051311/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489970128277/500000000000 : ℝ) ≤ (radius 8 (83/512 : ℝ)) ∧ (radius 8 (83/512 : ℝ)) ≤ (195988051311/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (83/512 : ℝ)) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (83/512 : ℝ)) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (83/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) (989970128277/1000000000000 : ℝ) (494985064139/500000000000 : ℝ) (247479829551/250000000000 : ℝ) (197983863641/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (83/512 : ℝ)) 1 (989970128277/1000000000000 : ℝ) (494985064139/500000000000 : ℝ) (247479829551/250000000000 : ℝ) (197983863641/200000000000 : ℝ) (24748618081/25000000000 : ℝ) (494972361621/500000000000 : ℝ) (494972361457/500000000000 : ℝ) (247486180729/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (83/512 : ℝ)) 2 (24748618081/25000000000 : ℝ) (494972361621/500000000000 : ℝ) (494972361457/500000000000 : ℝ) (247486180729/250000000000 : ℝ) (989944723077/1000000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (83/512 : ℝ)) 3 (989944723077/1000000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (83/512 : ℝ)) 4 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (83/512 : ℝ)) 5 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (83/512 : ℝ)) 6 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (83/512 : ℝ)) 7 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (83/512 : ℝ))) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ) (149911434869/250000000000 : ℝ) (599645739479/1000000000000 : ℝ) (446420742071/1000000000000 : ℝ) (446420742079/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 1 (149911434869/250000000000 : ℝ) (599645739479/1000000000000 : ℝ) (446420742071/1000000000000 : ℝ) (446420742079/1000000000000 : ℝ) (523033240773/1000000000000 : ℝ) (523033240779/1000000000000 : ℝ) (517391820573/1000000000000 : ℝ) (25869591029/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 2 (523033240773/1000000000000 : ℝ) (523033240779/1000000000000 : ℝ) (517391820573/1000000000000 : ℝ) (25869591029/50000000000 : ℝ) (520212530673/1000000000000 : ℝ) (13005313267/25000000000 : ℝ) (65025610419/125000000000 : ℝ) (520204883359/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 3 (520212530673/1000000000000 : ℝ) (13005313267/25000000000 : ℝ) (65025610419/125000000000 : ℝ) (520204883359/1000000000000 : ℝ) (130052176753/250000000000 : ℝ) (26010435351/50000000000 : ℝ) (260104353499/500000000000 : ℝ) (260104353503/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 4 (130052176753/250000000000 : ℝ) (26010435351/50000000000 : ℝ) (260104353499/500000000000 : ℝ) (260104353503/500000000000 : ℝ) (104041741401/200000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 5 (104041741401/200000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 6 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (83/512 : ℝ))) 7 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (83/512 : ℝ)) hmem 8 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (83/512 : ℝ))) hcmem 8 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (83/512 : ℝ)) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (206360493439/250000000000 : ℝ) (412720986887/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1716_exp_lower
  have heNumeric : (1028253217047/500000000000 : ℝ)/4 ≤ Real.exp (-332642861887/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028253217047/500000000000 : ℝ)/4 ≤ Real.exp ((41/256 : ℝ)-(412720986887/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (41/256 : ℝ) (83/512 : ℝ) (412720986887/500000000000 : ℝ) (1028253217047/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1717; no trusted numerical premise.
theorem cover8_leaf1717_exp_radius : (997439806337731487/1000000000000000000 : ℝ) ≤ Real.exp ((-21/1024 : ℝ)/8) ∧ Real.exp ((-21/1024 : ℝ)/8) ≤ (31169993948054109/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1717_exp_lower : (920237323250278199/1000000000000000000 : ℝ) ≤ Real.exp ((-664989457203/1000000000000 : ℝ)/8) ∧ Real.exp ((-664989457203/1000000000000 : ℝ)/8) ≤ (4601186616251391/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-664989457203/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1717_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028557899233/500000000000 : ℝ) ≤ 4*Real.exp (83/512 : ℝ)*Real.exp (-mu (radius 8 (21/128 : ℝ))) ∧ (20549/10000 : ℝ) < (1028557899233/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (21/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1717_exp_radius
  have hrNumeric : (97970104253/100000000000 : ℝ) ≤ Real.exp (-21/1024 : ℝ) ∧ Real.exp (-21/1024 : ℝ) ≤ (979701042531/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97970104253/100000000000 : ℝ) ≤ (radius 8 (21/128 : ℝ)) ∧ (radius 8 (21/128 : ℝ)) ≤ (979701042531/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (21/128 : ℝ)) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (21/128 : ℝ)) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (21/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) (197970104253/200000000000 : ℝ) (494925260633/500000000000 : ℝ) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (21/128 : ℝ)) 1 (197970104253/200000000000 : ℝ) (494925260633/500000000000 : ℝ) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ) (494912251771/500000000000 : ℝ) (989824503543/1000000000000 : ℝ) (1237280629/1250000000 : ℝ) (494912251601/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (21/128 : ℝ)) 2 (494912251771/500000000000 : ℝ) (989824503543/1000000000000 : ℝ) (1237280629/1250000000 : ℝ) (494912251601/500000000000 : ℝ) (989824503371/1000000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (21/128 : ℝ)) 3 (989824503371/1000000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (21/128 : ℝ)) 4 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (21/128 : ℝ)) 5 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (21/128 : ℝ)) 6 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (21/128 : ℝ)) 7 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (21/128 : ℝ))) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ) (600232064809/1000000000000 : ℝ) (150058016203/250000000000 : ℝ) (447732207483/1000000000000 : ℝ) (447732207491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 1 (600232064809/1000000000000 : ℝ) (150058016203/250000000000 : ℝ) (447732207483/1000000000000 : ℝ) (447732207491/1000000000000 : ℝ) (261991068073/500000000000 : ℝ) (65497767019/125000000000 : ℝ) (8100070339/15625000000 : ℝ) (518404501703/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 2 (261991068073/500000000000 : ℝ) (65497767019/125000000000 : ℝ) (8100070339/15625000000 : ℝ) (518404501703/1000000000000 : ℝ) (521193318921/1000000000000 : ℝ) (32574582433/62500000000 : ℝ) (521185857623/1000000000000 : ℝ) (52118585763/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 3 (521193318921/1000000000000 : ℝ) (32574582433/62500000000 : ℝ) (521185857623/1000000000000 : ℝ) (52118585763/100000000000 : ℝ) (32574349267/62500000000 : ℝ) (521189588279/1000000000000 : ℝ) (260594794129/500000000000 : ℝ) (260594794133/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 4 (32574349267/62500000000 : ℝ) (521189588279/1000000000000 : ℝ) (260594794129/500000000000 : ℝ) (260594794133/500000000000 : ℝ) (104237917653/200000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 5 (104237917653/200000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 6 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (21/128 : ℝ))) 7 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (21/128 : ℝ)) hmem 8 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (21/128 : ℝ))) hcmem 8 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (21/128 : ℝ)) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (165419766437/200000000000 : ℝ) (827098832203/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1717_exp_lower
  have heNumeric : (1028557899233/500000000000 : ℝ)/4 ≤ Real.exp (-664989457203/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028557899233/500000000000 : ℝ)/4 ≤ Real.exp ((83/512 : ℝ)-(827098832203/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (83/512 : ℝ) (21/128 : ℝ) (827098832203/1000000000000 : ℝ) (1028557899233/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1718; no trusted numerical premise.
theorem cover8_leaf1718_exp_radius : (99740936735498097/100000000000000000 : ℝ) ≤ Real.exp ((-85/4096 : ℝ)/8) ∧ Real.exp ((-85/4096 : ℝ)/8) ≤ (997409367354980971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1718_exp_lower : (460136452958275993/500000000000000000 : ℝ) ≤ Real.exp ((-66468012849/100000000000 : ℝ)/8) ∧ Real.exp ((-66468012849/100000000000 : ℝ)/8) ≤ (920272905916551987/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66468012849/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1718_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (658480711/320000000 : ℝ) ≤ 4*Real.exp (21/128 : ℝ)*Real.exp (-mu (radius 8 (85/512 : ℝ))) ∧ (20549/10000 : ℝ) < (658480711/320000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (85/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1718_exp_radius
  have hrNumeric : (9794618869/10000000000 : ℝ) ≤ Real.exp (-85/4096 : ℝ) ∧ Real.exp (-85/4096 : ℝ) ≤ (979461886901/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9794618869/10000000000 : ℝ) ≤ (radius 8 (85/512 : ℝ)) ∧ (radius 8 (85/512 : ℝ)) ≤ (979461886901/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (85/512 : ℝ)) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (85/512 : ℝ)) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (85/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) (19794618869/20000000000 : ℝ) (989730943451/1000000000000 : ℝ) (494838834091/500000000000 : ℝ) (123709708523/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (85/512 : ℝ)) 1 (19794618869/20000000000 : ℝ) (989730943451/1000000000000 : ℝ) (494838834091/500000000000 : ℝ) (123709708523/125000000000 : ℝ) (123713038227/125000000000 : ℝ) (494852152909/500000000000 : ℝ) (989704305457/1000000000000 : ℝ) (49485215273/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (85/512 : ℝ)) 2 (123713038227/125000000000 : ℝ) (494852152909/500000000000 : ℝ) (989704305457/1000000000000 : ℝ) (49485215273/50000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (85/512 : ℝ)) 3 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (85/512 : ℝ)) 4 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (85/512 : ℝ)) 5 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (85/512 : ℝ)) 6 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (85/512 : ℝ)) 7 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (85/512 : ℝ))) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ) (600814696483/1000000000000 : ℝ) (600814696487/1000000000000 : ℝ) (44903161689/100000000000 : ℝ) (449031616897/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 1 (600814696483/1000000000000 : ℝ) (600814696487/1000000000000 : ℝ) (44903161689/100000000000 : ℝ) (449031616897/1000000000000 : ℝ) (262461578343/500000000000 : ℝ) (131230789173/250000000000 : ℝ) (51940811951/100000000000 : ℝ) (129852029879/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 2 (262461578343/500000000000 : ℝ) (131230789173/250000000000 : ℝ) (51940811951/100000000000 : ℝ) (129852029879/250000000000 : ℝ) (261082819049/500000000000 : ℝ) (65270704763/125000000000 : ℝ) (13053958923/25000000000 : ℝ) (522158356927/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 3 (261082819049/500000000000 : ℝ) (65270704763/125000000000 : ℝ) (13053958923/25000000000 : ℝ) (522158356927/1000000000000 : ℝ) (522161997509/1000000000000 : ℝ) (130540499379/250000000000 : ℝ) (65270249687/125000000000 : ℝ) (522161997503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 4 (522161997509/1000000000000 : ℝ) (130540499379/250000000000 : ℝ) (65270249687/125000000000 : ℝ) (522161997503/1000000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 5 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 6 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (85/512 : ℝ))) 7 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (85/512 : ℝ)) hmem 8 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (85/512 : ℝ))) hcmem 8 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (85/512 : ℝ)) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (414371314237/500000000000 : ℝ) (82874262849/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1718_exp_lower
  have heNumeric : (658480711/320000000 : ℝ)/4 ≤ Real.exp (-66468012849/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (658480711/320000000 : ℝ)/4 ≤ Real.exp ((21/128 : ℝ)-(82874262849/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (21/128 : ℝ) (85/512 : ℝ) (82874262849/100000000000 : ℝ) (658480711/320000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1719; no trusted numerical premise.
theorem cover8_leaf1719_exp_radius : (997378929301140313/1000000000000000000 : ℝ) ≤ Real.exp ((-43/2048 : ℝ)/8) ∧ Real.exp ((-43/2048 : ℝ)/8) ≤ (498689464650570157/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1719_exp_lower : (920309961824079871/1000000000000000000 : ℝ) ≤ Real.exp ((-1297574229/1953125000 : ℝ)/8) ∧ Real.exp ((-1297574229/1953125000 : ℝ)/8) ≤ (224685049273457/244140625000000 : ℝ) := by
  have h := exp_small_bounds ((-1297574229/1953125000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1719_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2058415178463/1000000000000 : ℝ) ≤ 4*Real.exp (85/512 : ℝ)*Real.exp (-mu (radius 8 (43/256 : ℝ))) ∧ (20549/10000 : ℝ) < (2058415178463/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (43/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1719_exp_radius
  have hrNumeric : (979222789651/1000000000000 : ℝ) ≤ Real.exp (-43/2048 : ℝ) ∧ Real.exp (-43/2048 : ℝ) ≤ (244805697413/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979222789651/1000000000000 : ℝ) ≤ (radius 8 (43/256 : ℝ)) ∧ (radius 8 (43/256 : ℝ)) ≤ (244805697413/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (43/256 : ℝ)) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (43/256 : ℝ)) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (43/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) (39584455793/40000000000 : ℝ) (494805697413/500000000000 : ℝ) (494778432647/500000000000 : ℝ) (197911373059/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (43/256 : ℝ)) 1 (39584455793/40000000000 : ℝ) (494805697413/500000000000 : ℝ) (494778432647/500000000000 : ℝ) (197911373059/200000000000 : ℝ) (989584130059/1000000000000 : ℝ) (989584130061/1000000000000 : ℝ) (989584129683/1000000000000 : ℝ) (197916825937/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (43/256 : ℝ)) 2 (989584130059/1000000000000 : ℝ) (989584130061/1000000000000 : ℝ) (989584129683/1000000000000 : ℝ) (197916825937/200000000000 : ℝ) (989584129871/1000000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (43/256 : ℝ)) 3 (989584129871/1000000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (43/256 : ℝ)) 4 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (43/256 : ℝ)) 5 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (43/256 : ℝ)) 6 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (43/256 : ℝ)) 7 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (43/256 : ℝ))) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ) (601393698307/1000000000000 : ℝ) (601393698311/1000000000000 : ℝ) (450319216351/1000000000000 : ℝ) (225159608179/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 1 (601393698307/1000000000000 : ℝ) (601393698311/1000000000000 : ℝ) (450319216351/1000000000000 : ℝ) (225159608179/500000000000 : ℝ) (525856457329/1000000000000 : ℝ) (105171291467/200000000000 : ℝ) (104080572431/200000000000 : ℝ) (260201431081/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 2 (525856457329/1000000000000 : ℝ) (105171291467/200000000000 : ℝ) (104080572431/200000000000 : ℝ) (260201431081/500000000000 : ℝ) (261564829871/500000000000 : ℝ) (523129659749/1000000000000 : ℝ) (261561276509/500000000000 : ℝ) (261561276513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 3 (261564829871/500000000000 : ℝ) (523129659749/1000000000000 : ℝ) (261561276509/500000000000 : ℝ) (261561276513/500000000000 : ℝ) (26156305319/50000000000 : ℝ) (130781526597/250000000000 : ℝ) (523126106367/1000000000000 : ℝ) (65390763297/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 4 (26156305319/50000000000 : ℝ) (130781526597/250000000000 : ℝ) (523126106367/1000000000000 : ℝ) (65390763297/125000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 5 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 6 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (43/256 : ℝ))) 7 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (43/256 : ℝ)) hmem 8 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (43/256 : ℝ))) hcmem 8 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (43/256 : ℝ)) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (83037363023/100000000000 : ℝ) (103796703781/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1719_exp_lower
  have heNumeric : (2058415178463/1000000000000 : ℝ)/4 ≤ Real.exp (-1297574229/1953125000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2058415178463/1000000000000 : ℝ)/4 ≤ Real.exp ((85/512 : ℝ)-(103796703781/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (85/512 : ℝ) (43/256 : ℝ) (103796703781/125000000000 : ℝ) (2058415178463/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1720; no trusted numerical premise.
theorem cover8_leaf1720_exp_radius : (997318055980075189/1000000000000000000 : ℝ) ≤ Real.exp ((-11/512 : ℝ)/8) ∧ Real.exp ((-11/512 : ℝ)/8) ≤ (99731805598007519/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1720_exp_lower : (36806547961448203/40000000000000000 : ℝ) ≤ Real.exp ((-665629528259/1000000000000 : ℝ)/8) ∧ Real.exp ((-665629528259/1000000000000 : ℝ)/8) ≤ (230040924759051269/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665629528259/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1720_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027899759743/500000000000 : ℝ) ≤ 4*Real.exp (43/256 : ℝ)*Real.exp (-mu (radius 8 (11/64 : ℝ))) ∧ (20549/10000 : ℝ) < (1027899759743/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (11/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1720_exp_radius
  have hrNumeric : (244686192559/250000000000 : ℝ) ≤ Real.exp (-11/512 : ℝ) ∧ Real.exp (-11/512 : ℝ) ≤ (978744770237/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (244686192559/250000000000 : ℝ) ≤ (radius 8 (11/64 : ℝ)) ∧ (radius 8 (11/64 : ℝ)) ≤ (978744770237/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (11/64 : ℝ)) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (11/64 : ℝ)) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (11/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) (494686192559/500000000000 : ℝ) (989372385119/1000000000000 : ℝ) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (11/64 : ℝ)) 1 (494686192559/500000000000 : ℝ) (989372385119/1000000000000 : ℝ) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ) (494671922217/500000000000 : ℝ) (247335961109/250000000000 : ℝ) (494671922011/500000000000 : ℝ) (123667980503/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (11/64 : ℝ)) 2 (494671922217/500000000000 : ℝ) (247335961109/250000000000 : ℝ) (494671922011/500000000000 : ℝ) (123667980503/125000000000 : ℝ) (247335961057/250000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (11/64 : ℝ)) 3 (247335961057/250000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (11/64 : ℝ)) 4 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (11/64 : ℝ)) 5 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (11/64 : ℝ)) 6 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (11/64 : ℝ)) 7 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (11/64 : ℝ))) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ) (24101642341/40000000000 : ℝ) (18829408079/31250000000 : ℝ) (226429965469/500000000000 : ℝ) (90571986189/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 1 (24101642341/40000000000 : ℝ) (18829408079/31250000000 : ℝ) (226429965469/500000000000 : ℝ) (90571986189/200000000000 : ℝ) (527700494731/1000000000000 : ℝ) (527700494737/1000000000000 : ℝ) (522366444319/1000000000000 : ℝ) (20894657773/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 2 (527700494731/1000000000000 : ℝ) (527700494737/1000000000000 : ℝ) (522366444319/1000000000000 : ℝ) (20894657773/40000000000 : ℝ) (21001338781/40000000000 : ℝ) (525033469531/1000000000000 : ℝ) (105005339121/200000000000 : ℝ) (131256673903/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 3 (21001338781/40000000000 : ℝ) (525033469531/1000000000000 : ℝ) (105005339121/200000000000 : ℝ) (131256673903/250000000000 : ℝ) (105006016513/200000000000 : ℝ) (131257520643/250000000000 : ℝ) (262515041277/500000000000 : ℝ) (525030082561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 4 (105006016513/200000000000 : ℝ) (131257520643/250000000000 : ℝ) (262515041277/500000000000 : ℝ) (525030082561/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 5 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 6 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (11/64 : ℝ))) 7 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (11/64 : ℝ)) hmem 8 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (11/64 : ℝ))) hcmem 8 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (11/64 : ℝ)) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (833598278243/1000000000000 : ℝ) (833598278259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1720_exp_lower
  have heNumeric : (1027899759743/500000000000 : ℝ)/4 ≤ Real.exp (-665629528259/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027899759743/500000000000 : ℝ)/4 ≤ Real.exp ((43/256 : ℝ)-(833598278259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (43/256 : ℝ) (11/64 : ℝ) (833598278259/1000000000000 : ℝ) (1027899759743/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1721; no trusted numerical premise.
theorem cover8_leaf1721_exp_radius : (199451437274861869/200000000000000000 : ℝ) ≤ Real.exp ((-45/2048 : ℝ)/8) ∧ Real.exp ((-45/2048 : ℝ)/8) ≤ (498628593187154673/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-45/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1721_exp_lower : (920247641999864377/1000000000000000000 : ℝ) ≤ Real.exp ((-664899752589/1000000000000 : ℝ)/8) ∧ Real.exp ((-664899752589/1000000000000 : ℝ)/8) ≤ (460123820999932189/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-664899752589/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1721_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028650169761/500000000000 : ℝ) ≤ 4*Real.exp (11/64 : ℝ)*Real.exp (-mu (radius 8 (45/256 : ℝ))) ∧ (20549/10000 : ℝ) < (1028650169761/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (45/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1721_exp_radius
  have hrNumeric : (978266984173/1000000000000 : ℝ) ≤ Real.exp (-45/2048 : ℝ) ∧ Real.exp (-45/2048 : ℝ) ≤ (489133492087/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978266984173/1000000000000 : ℝ) ≤ (radius 8 (45/256 : ℝ)) ∧ (radius 8 (45/256 : ℝ)) ≤ (489133492087/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (45/256 : ℝ)) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (45/256 : ℝ)) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (45/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) (494566746043/500000000000 : ℝ) (989133492087/1000000000000 : ℝ) (123634225147/125000000000 : ℝ) (989073801177/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (45/256 : ℝ)) 1 (494566746043/500000000000 : ℝ) (989133492087/1000000000000 : ℝ) (123634225147/125000000000 : ℝ) (989073801177/1000000000000 : ℝ) (989103646631/1000000000000 : ℝ) (123637955829/125000000000 : ℝ) (49455182309/50000000000 : ℝ) (494551823091/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (45/256 : ℝ)) 2 (989103646631/1000000000000 : ℝ) (123637955829/125000000000 : ℝ) (49455182309/50000000000 : ℝ) (494551823091/500000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (45/256 : ℝ)) 3 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (45/256 : ℝ)) 4 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (45/256 : ℝ)) 5 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (45/256 : ℝ)) 6 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (45/256 : ℝ)) 7 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (45/256 : ℝ))) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ) (603674620417/1000000000000 : ℝ) (603674620421/1000000000000 : ℝ) (455356169207/1000000000000 : ℝ) (227678084607/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 1 (603674620417/1000000000000 : ℝ) (603674620421/1000000000000 : ℝ) (455356169207/1000000000000 : ℝ) (227678084607/500000000000 : ℝ) (132378848703/250000000000 : ℝ) (264757697409/500000000000 : ℝ) (20971865443/40000000000 : ℝ) (262148318041/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 2 (132378848703/250000000000 : ℝ) (264757697409/500000000000 : ℝ) (20971865443/40000000000 : ℝ) (262148318041/500000000000 : ℝ) (526906015443/1000000000000 : ℝ) (10538120309/20000000000 : ℝ) (526899554231/1000000000000 : ℝ) (526899554239/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 3 (526906015443/1000000000000 : ℝ) (10538120309/20000000000 : ℝ) (526899554231/1000000000000 : ℝ) (526899554239/1000000000000 : ℝ) (526902784837/1000000000000 : ℝ) (105380556969/200000000000 : ℝ) (526902784827/1000000000000 : ℝ) (105380556967/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 4 (526902784837/1000000000000 : ℝ) (105380556969/200000000000 : ℝ) (526902784827/1000000000000 : ℝ) (105380556967/200000000000 : ℝ) (8232856013/15625000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 5 (8232856013/15625000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 6 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (45/256 : ℝ))) 7 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (45/256 : ℝ)) hmem 8 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (45/256 : ℝ))) hcmem 8 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (45/256 : ℝ)) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (209193688143/250000000000 : ℝ) (836774752589/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1721_exp_lower
  have heNumeric : (1028650169761/500000000000 : ℝ)/4 ≤ Real.exp (-664899752589/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028650169761/500000000000 : ℝ)/4 ≤ Real.exp ((11/64 : ℝ)-(836774752589/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (11/64 : ℝ) (45/256 : ℝ) (836774752589/1000000000000 : ℝ) (1028650169761/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1722; no trusted numerical premise.
theorem cover8_leaf1722_exp_radius : (997196320483616023/1000000000000000000 : ℝ) ≤ Real.exp ((-23/1024 : ℝ)/8) ∧ Real.exp ((-23/1024 : ℝ)/8) ≤ (124649540060452003/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-23/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1722_exp_lower : (460168460536541829/500000000000000000 : ℝ) ≤ Real.exp ((-83015457423/125000000000 : ℝ)/8) ∧ Real.exp ((-83015457423/125000000000 : ℝ)/8) ≤ (920336921073083659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83015457423/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1722_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2058897616073/1000000000000 : ℝ) ≤ 4*Real.exp (45/256 : ℝ)*Real.exp (-mu (radius 8 (23/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2058897616073/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (23/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1722_exp_radius
  have hrNumeric : (977789431347/1000000000000 : ℝ) ≤ Real.exp (-23/1024 : ℝ) ∧ Real.exp (-23/1024 : ℝ) ≤ (244447357837/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (977789431347/1000000000000 : ℝ) ≤ (radius 8 (23/128 : ℝ)) ∧ (radius 8 (23/128 : ℝ)) ≤ (244447357837/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (23/128 : ℝ)) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (23/128 : ℝ)) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (23/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) (988894715673/1000000000000 : ℝ) (494447357837/500000000000 : ℝ) (494416178777/500000000000 : ℝ) (247208089389/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (23/128 : ℝ)) 1 (988894715673/1000000000000 : ℝ) (494447357837/500000000000 : ℝ) (494416178777/500000000000 : ℝ) (247208089389/250000000000 : ℝ) (988863536613/1000000000000 : ℝ) (197772707323/200000000000 : ℝ) (988863536121/1000000000000 : ℝ) (247215884031/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (23/128 : ℝ)) 2 (988863536613/1000000000000 : ℝ) (197772707323/200000000000 : ℝ) (988863536121/1000000000000 : ℝ) (247215884031/250000000000 : ℝ) (988863536367/1000000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (23/128 : ℝ)) 3 (988863536367/1000000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (23/128 : ℝ)) 4 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (23/128 : ℝ)) 5 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (23/128 : ℝ)) 6 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (23/128 : ℝ)) 7 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (23/128 : ℝ))) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ) (604794832821/1000000000000 : ℝ) (75599354103/125000000000 : ℝ) (28613102443/62500000000 : ℝ) (91561927819/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 1 (604794832821/1000000000000 : ℝ) (75599354103/125000000000 : ℝ) (28613102443/62500000000 : ℝ) (91561927819/200000000000 : ℝ) (265651117977/500000000000 : ℝ) (13282555899/25000000000 : ℝ) (105238947949/200000000000 : ℝ) (65774342469/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 2 (265651117977/500000000000 : ℝ) (13282555899/25000000000 : ℝ) (105238947949/200000000000 : ℝ) (65774342469/125000000000 : ℝ) (528748487849/1000000000000 : ℝ) (33046780491/62500000000 : ℝ) (52874232077/100000000000 : ℝ) (528742320777/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 3 (528748487849/1000000000000 : ℝ) (33046780491/62500000000 : ℝ) (52874232077/100000000000 : ℝ) (528742320777/1000000000000 : ℝ) (528745404309/1000000000000 : ℝ) (528745404317/1000000000000 : ℝ) (5287454043/10000000000 : ℝ) (132186351077/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 4 (528745404309/1000000000000 : ℝ) (528745404317/1000000000000 : ℝ) (5287454043/10000000000 : ℝ) (132186351077/250000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 5 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 6 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (23/128 : ℝ))) 7 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (23/128 : ℝ)) hmem 8 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (23/128 : ℝ))) hcmem 8 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (23/128 : ℝ)) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (419952454683/500000000000 : ℝ) (104988113673/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1722_exp_lower
  have heNumeric : (2058897616073/1000000000000 : ℝ)/4 ≤ Real.exp (-83015457423/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2058897616073/1000000000000 : ℝ)/4 ≤ Real.exp ((45/256 : ℝ)-(104988113673/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (45/256 : ℝ) (23/128 : ℝ) (104988113673/125000000000 : ℝ) (2058897616073/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1723; no trusted numerical premise.
theorem cover8_leaf1723_exp_radius : (997135458307768481/1000000000000000000 : ℝ) ≤ Real.exp ((-47/2048 : ℝ)/8) ∧ Real.exp ((-47/2048 : ℝ)/8) ≤ (498567729153884241/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-47/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1723_exp_lower : (920431336960288773/1000000000000000000 : ℝ) ≤ Real.exp ((-331651497161/500000000000 : ℝ)/8) ∧ Real.exp ((-331651497161/500000000000 : ℝ)/8) ≤ (460215668480144387/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-331651497161/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1723_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2060587974927/1000000000000 : ℝ) ≤ 4*Real.exp (23/128 : ℝ)*Real.exp (-mu (radius 8 (47/256 : ℝ))) ∧ (20549/10000 : ℝ) < (2060587974927/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (47/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1723_exp_radius
  have hrNumeric : (977312111643/1000000000000 : ℝ) ≤ Real.exp (-47/2048 : ℝ) ∧ Real.exp (-47/2048 : ℝ) ≤ (244328027911/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (977312111643/1000000000000 : ℝ) ≤ (radius 8 (47/256 : ℝ)) ∧ (radius 8 (47/256 : ℝ)) ≤ (244328027911/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (47/256 : ℝ)) (977312111643/1000000000000 : ℝ) (244328027911/250000000000 : ℝ) (21180424083/100000000000 : ℝ) (52951060209/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (47/256 : ℝ)) (977312111643/1000000000000 : ℝ) (244328027911/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (47/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (977312111643/1000000000000 : ℝ) (244328027911/250000000000 : ℝ) (988656055821/1000000000000 : ℝ) (494328027911/500000000000 : ℝ) (988590972871/1000000000000 : ℝ) (123573871609/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (47/256 : ℝ)) 1 (988656055821/1000000000000 : ℝ) (494328027911/500000000000 : ℝ) (988590972871/1000000000000 : ℝ) (123573871609/125000000000 : ℝ) (494311757173/500000000000 : ℝ) (988623514347/1000000000000 : ℝ) (98862351381/100000000000 : ℝ) (247155878453/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (47/256 : ℝ)) 2 (494311757173/500000000000 : ℝ) (988623514347/1000000000000 : ℝ) (98862351381/100000000000 : ℝ) (247155878453/250000000000 : ℝ) (494311757039/500000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (47/256 : ℝ)) 3 (494311757039/500000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (47/256 : ℝ)) 4 (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (47/256 : ℝ)) 5 (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (47/256 : ℝ)) 6 (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (47/256 : ℝ)) 7 (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (47/256 : ℝ))) (21180424083/100000000000 : ℝ) (52951060209/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21180424083/100000000000 : ℝ) (52951060209/250000000000 : ℝ) (121180424083/200000000000 : ℝ) (302951060209/500000000000 : ℝ) (230110973679/500000000000 : ℝ) (92044389473/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 1 (121180424083/200000000000 : ℝ) (302951060209/500000000000 : ℝ) (230110973679/500000000000 : ℝ) (92044389473/200000000000 : ℝ) (266531016943/500000000000 : ℝ) (133265508473/250000000000 : ℝ) (105612395819/200000000000 : ℝ) (528061979101/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 2 (266531016943/500000000000 : ℝ) (133265508473/250000000000 : ℝ) (105612395819/200000000000 : ℝ) (528061979101/1000000000000 : ℝ) (53056200649/100000000000 : ℝ) (530562006497/1000000000000 : ℝ) (530556116347/1000000000000 : ℝ) (265278058177/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 3 (53056200649/100000000000 : ℝ) (530562006497/1000000000000 : ℝ) (530556116347/1000000000000 : ℝ) (265278058177/500000000000 : ℝ) (265279530709/500000000000 : ℝ) (265279530713/500000000000 : ℝ) (53055906141/100000000000 : ℝ) (265279530709/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 4 (265279530709/500000000000 : ℝ) (265279530713/500000000000 : ℝ) (53055906141/100000000000 : ℝ) (265279530709/500000000000 : ℝ) (265279530707/500000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 5 (265279530707/500000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 6 (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (47/256 : ℝ))) 7 (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (47/256 : ℝ)) hmem 8 (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (47/256 : ℝ))) hcmem 8 (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (47/256 : ℝ)) (988623514077/1000000000000 : ℝ) (6178896963/6250000000 : ℝ) (530559061413/1000000000000 : ℝ) (265279530711/500000000000 : ℝ) (26343452947/31250000000 : ℝ) (421495247161/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1723_exp_lower
  have heNumeric : (2060587974927/1000000000000 : ℝ)/4 ≤ Real.exp (-331651497161/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2060587974927/1000000000000 : ℝ)/4 ≤ Real.exp ((23/128 : ℝ)-(421495247161/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (23/128 : ℝ) (47/256 : ℝ) (421495247161/500000000000 : ℝ) (2060587974927/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1724; no trusted numerical premise.
theorem cover8_leaf1724_exp_radius : (997074599846539989/1000000000000000000 : ℝ) ≤ Real.exp ((-3/128 : ℝ)/8) ∧ Real.exp ((-3/128 : ℝ)/8) ≤ (99707459984653999/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/128 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1724_exp_lower : (460265351036789727/500000000000000000 : ℝ) ≤ Real.exp ((-132487880277/200000000000 : ℝ)/8) ∧ Real.exp ((-132487880277/200000000000 : ℝ)/8) ≤ (184106140414715891/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-132487880277/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1724_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (515592063189/250000000000 : ℝ) ≤ 4*Real.exp (47/256 : ℝ)*Real.exp (-mu (radius 8 (3/16 : ℝ))) ∧ (20549/10000 : ℝ) < (515592063189/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (3/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1724_exp_radius
  have hrNumeric : (19536700499/20000000000 : ℝ) ≤ Real.exp (-3/128 : ℝ) ∧ Real.exp (-3/128 : ℝ) ≤ (976835024951/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19536700499/20000000000 : ℝ) ≤ (radius 8 (3/16 : ℝ)) ∧ (radius 8 (3/16 : ℝ)) ≤ (976835024951/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (3/16 : ℝ)) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (3/16 : ℝ)) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (3/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) (39536700499/40000000000 : ℝ) (247104378119/250000000000 : ℝ) (988349647113/1000000000000 : ℝ) (197669929423/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (3/16 : ℝ)) 1 (39536700499/40000000000 : ℝ) (247104378119/250000000000 : ℝ) (988349647113/1000000000000 : ℝ) (197669929423/200000000000 : ℝ) (494191789897/500000000000 : ℝ) (247095894949/250000000000 : ℝ) (988383579211/1000000000000 : ℝ) (494191789607/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (3/16 : ℝ)) 2 (494191789897/500000000000 : ℝ) (247095894949/250000000000 : ℝ) (988383579211/1000000000000 : ℝ) (494191789607/500000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (3/16 : ℝ)) 3 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (3/16 : ℝ)) 4 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (3/16 : ℝ)) 5 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (3/16 : ℝ)) 6 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (3/16 : ℝ)) 7 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (3/16 : ℝ))) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ) (303498442751/500000000000 : ℝ) (121399377101/200000000000 : ℝ) (231297303813/500000000000 : ℝ) (28912162977/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 1 (303498442751/500000000000 : ℝ) (121399377101/200000000000 : ℝ) (231297303813/500000000000 : ℝ) (28912162977/62500000000 : ℝ) (133698936641/250000000000 : ℝ) (534795746569/1000000000000 : ℝ) (529899505641/1000000000000 : ℝ) (529899505647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 2 (133698936641/250000000000 : ℝ) (534795746569/1000000000000 : ℝ) (529899505641/1000000000000 : ℝ) (529899505647/1000000000000 : ℝ) (266173813051/500000000000 : ℝ) (133086906527/250000000000 : ℝ) (133085499239/250000000000 : ℝ) (266170998481/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 3 (266173813051/500000000000 : ℝ) (133086906527/250000000000 : ℝ) (133085499239/250000000000 : ℝ) (266170998481/500000000000 : ℝ) (532344811529/1000000000000 : ℝ) (106468962307/200000000000 : ℝ) (532344811521/1000000000000 : ℝ) (66543101441/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 4 (532344811529/1000000000000 : ℝ) (106468962307/200000000000 : ℝ) (532344811521/1000000000000 : ℝ) (66543101441/125000000000 : ℝ) (21293792461/40000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 5 (21293792461/40000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 6 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (3/16 : ℝ))) 7 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (3/16 : ℝ)) hmem 8 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (3/16 : ℝ))) hcmem 8 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (3/16 : ℝ)) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (846033151369/1000000000000 : ℝ) (169206630277/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1724_exp_lower
  have heNumeric : (515592063189/250000000000 : ℝ)/4 ≤ Real.exp (-132487880277/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (515592063189/250000000000 : ℝ)/4 ≤ Real.exp ((47/256 : ℝ)-(169206630277/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (47/256 : ℝ) (3/16 : ℝ) (169206630277/200000000000 : ℝ) (515592063189/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1700_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1700_certificate
#check SmaleRate.Proofs.cover8_leaf1701_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1701_certificate
#check SmaleRate.Proofs.cover8_leaf1702_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1702_certificate
#check SmaleRate.Proofs.cover8_leaf1703_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1703_certificate
#check SmaleRate.Proofs.cover8_leaf1704_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1704_certificate
#check SmaleRate.Proofs.cover8_leaf1705_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1705_certificate
#check SmaleRate.Proofs.cover8_leaf1706_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1706_certificate
#check SmaleRate.Proofs.cover8_leaf1707_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1707_certificate
#check SmaleRate.Proofs.cover8_leaf1708_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1708_certificate
#check SmaleRate.Proofs.cover8_leaf1709_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1709_certificate
#check SmaleRate.Proofs.cover8_leaf1710_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1710_certificate
#check SmaleRate.Proofs.cover8_leaf1711_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1711_certificate
#check SmaleRate.Proofs.cover8_leaf1712_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1712_certificate
#check SmaleRate.Proofs.cover8_leaf1713_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1713_certificate
#check SmaleRate.Proofs.cover8_leaf1714_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1714_certificate
#check SmaleRate.Proofs.cover8_leaf1715_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1715_certificate
#check SmaleRate.Proofs.cover8_leaf1716_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1716_certificate
#check SmaleRate.Proofs.cover8_leaf1717_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1717_certificate
#check SmaleRate.Proofs.cover8_leaf1718_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1718_certificate
#check SmaleRate.Proofs.cover8_leaf1719_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1719_certificate
#check SmaleRate.Proofs.cover8_leaf1720_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1720_certificate
#check SmaleRate.Proofs.cover8_leaf1721_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1721_certificate
#check SmaleRate.Proofs.cover8_leaf1722_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1722_certificate
#check SmaleRate.Proofs.cover8_leaf1723_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1723_certificate
#check SmaleRate.Proofs.cover8_leaf1724_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1724_certificate
