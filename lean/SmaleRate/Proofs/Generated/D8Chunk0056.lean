/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1400; no trusted numerical premise.
theorem cover8_leaf1400_exp_radius : (997985011641042591/1000000000000000000 : ℝ) ≤ Real.exp ((-2115/131072 : ℝ)/8) ∧ Real.exp ((-2115/131072 : ℝ)/8) ≤ (31187031613782581/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2115/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1400_exp_lower : (230028351458410793/250000000000000000 : ℝ) ≤ Real.exp ((-21314137427289/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314137427289/32000000000000 : ℝ)/8) ≤ (920113405833643173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314137427289/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1400_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450392027/500000000000 : ℝ) ≤ 4*Real.exp (16919/131072 : ℝ)*Real.exp (-mu (radius 8 (2115/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450392027/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2115/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1400_exp_radius
  have hrNumeric : (983993321119/1000000000000 : ℝ) ≤ Real.exp (-2115/131072 : ℝ) ∧ Real.exp (-2115/131072 : ℝ) ≤ (6149958257/6250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983993321119/1000000000000 : ℝ) ≤ (radius 8 (2115/16384 : ℝ)) ∧ (radius 8 (2115/16384 : ℝ)) ≤ (6149958257/6250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2115/16384 : ℝ)) (983993321119/1000000000000 : ℝ) (6149958257/6250000000 : ℝ) (178205342207/1000000000000 : ℝ) (178205342213/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2115/16384 : ℝ)) (983993321119/1000000000000 : ℝ) (6149958257/6250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983993321119/1000000000000 : ℝ) (6149958257/6250000000 : ℝ) (991996660559/1000000000000 : ℝ) (12399958257/12500000000 : ℝ) (247991093731/250000000000 : ℝ) (39678574997/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 1 (991996660559/1000000000000 : ℝ) (12399958257/12500000000 : ℝ) (247991093731/250000000000 : ℝ) (39678574997/40000000000 : ℝ) (991980517741/1000000000000 : ℝ) (991980517743/1000000000000 : ℝ) (99198051761/100000000000 : ℝ) (247995129403/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 2 (991980517741/1000000000000 : ℝ) (991980517743/1000000000000 : ℝ) (99198051761/100000000000 : ℝ) (247995129403/250000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 3 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 4 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 5 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 6 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2115/16384 : ℝ)) 7 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2115/16384 : ℝ))) (178205342207/1000000000000 : ℝ) (178205342213/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178205342207/1000000000000 : ℝ) (178205342213/1000000000000 : ℝ) (589102671103/1000000000000 : ℝ) (589102671107/1000000000000 : ℝ) (84428749181/200000000000 : ℝ) (422143745913/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 1 (589102671103/1000000000000 : ℝ) (589102671107/1000000000000 : ℝ) (84428749181/200000000000 : ℝ) (422143745913/1000000000000 : ℝ) (63202901063/125000000000 : ℝ) (50562320851/100000000000 : ℝ) (19947371087/40000000000 : ℝ) (249342138591/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 2 (63202901063/125000000000 : ℝ) (50562320851/100000000000 : ℝ) (19947371087/40000000000 : ℝ) (249342138591/500000000000 : ℝ) (502153742839/1000000000000 : ℝ) (251076871423/500000000000 : ℝ) (125535439283/250000000000 : ℝ) (502141757139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 3 (502153742839/1000000000000 : ℝ) (251076871423/500000000000 : ℝ) (125535439283/250000000000 : ℝ) (502141757139/1000000000000 : ℝ) (100429549997/200000000000 : ℝ) (502147749993/1000000000000 : ℝ) (502147749949/1000000000000 : ℝ) (502147749957/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 4 (100429549997/200000000000 : ℝ) (502147749993/1000000000000 : ℝ) (502147749949/1000000000000 : ℝ) (502147749957/1000000000000 : ℝ) (502147749967/1000000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 5 (502147749967/1000000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 6 (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2115/16384 : ℝ))) 7 (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2115/16384 : ℝ)) hmem 8 (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2115/16384 : ℝ))) hcmem 8 (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2115/16384 : ℝ)) (39679220707/40000000000 : ℝ) (495990258839/500000000000 : ℝ) (251073874983/500000000000 : ℝ) (20085909999/40000000000 : ℝ) (795148520659/1000000000000 : ℝ) (795148520677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1400_exp_lower
  have heNumeric : (1027450392027/500000000000 : ℝ)/4 ≤ Real.exp (-21314137427289/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450392027/500000000000 : ℝ)/4 ≤ Real.exp ((16919/131072 : ℝ)-(795148520677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16919/131072 : ℝ) (2115/16384 : ℝ) (795148520677/1000000000000 : ℝ) (1027450392027/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1401; no trusted numerical premise.
theorem cover8_leaf1401_exp_radius : (498992446335982731/500000000000000000 : ℝ) ≤ Real.exp ((-16921/1048576 : ℝ)/8) ∧ Real.exp ((-16921/1048576 : ℝ)/8) ≤ (997984892671965463/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16921/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1401_exp_lower : (36804536497190691/40000000000000000 : ℝ) ≤ Real.exp ((-2664266949009/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664266949009/4000000000000 : ℝ)/8) ≤ (230028353107441819/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664266949009/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1401_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900901903/1000000000000 : ℝ) ≤ 4*Real.exp (2115/16384 : ℝ)*Real.exp (-mu (radius 8 (16921/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900901903/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16921/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1401_exp_radius
  have hrNumeric : (98399238271/100000000000 : ℝ) ≤ Real.exp (-16921/1048576 : ℝ) ∧ Real.exp (-16921/1048576 : ℝ) ≤ (983992382711/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98399238271/100000000000 : ℝ) ≤ (radius 8 (16921/131072 : ℝ)) ∧ (radius 8 (16921/131072 : ℝ)) ≤ (983992382711/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16921/131072 : ℝ)) (98399238271/100000000000 : ℝ) (983992382711/1000000000000 : ℝ) (89105261863/500000000000 : ℝ) (44552630933/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16921/131072 : ℝ)) (98399238271/100000000000 : ℝ) (983992382711/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98399238271/100000000000 : ℝ) (983992382711/1000000000000 : ℝ) (198399238271/200000000000 : ℝ) (247999047839/250000000000 : ℝ) (495981950959/500000000000 : ℝ) (6199774387/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 1 (198399238271/200000000000 : ℝ) (247999047839/250000000000 : ℝ) (495981950959/500000000000 : ℝ) (6199774387/6250000000 : ℝ) (247995011659/250000000000 : ℝ) (495990023319/500000000000 : ℝ) (198396009301/200000000000 : ℝ) (991980046507/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 2 (247995011659/250000000000 : ℝ) (495990023319/500000000000 : ℝ) (198396009301/200000000000 : ℝ) (991980046507/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 3 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 4 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 5 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 6 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16921/131072 : ℝ)) 7 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16921/131072 : ℝ))) (89105261863/500000000000 : ℝ) (44552630933/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89105261863/500000000000 : ℝ) (44552630933/250000000000 : ℝ) (589105261863/1000000000000 : ℝ) (294552630933/500000000000 : ℝ) (42214988301/100000000000 : ℝ) (211074941509/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 1 (589105261863/1000000000000 : ℝ) (294552630933/500000000000 : ℝ) (42214988301/100000000000 : ℝ) (211074941509/500000000000 : ℝ) (126406893109/250000000000 : ℝ) (252813786221/500000000000 : ℝ) (498688998651/1000000000000 : ℝ) (249344499329/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 2 (126406893109/250000000000 : ℝ) (252813786221/500000000000 : ℝ) (498688998651/1000000000000 : ℝ) (249344499329/500000000000 : ℝ) (502158285543/1000000000000 : ℝ) (10043165711/20000000000 : ℝ) (502146301179/1000000000000 : ℝ) (502146301187/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 3 (502158285543/1000000000000 : ℝ) (10043165711/20000000000 : ℝ) (502146301179/1000000000000 : ℝ) (502146301187/1000000000000 : ℝ) (502152293361/1000000000000 : ℝ) (502152293369/1000000000000 : ℝ) (20086091733/40000000000 : ℝ) (502152293333/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 4 (502152293361/1000000000000 : ℝ) (502152293369/1000000000000 : ℝ) (20086091733/40000000000 : ℝ) (502152293333/1000000000000 : ℝ) (502152293343/1000000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 5 (502152293343/1000000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 6 (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16921/131072 : ℝ))) 7 (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16921/131072 : ℝ)) hmem 8 (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16921/131072 : ℝ))) hcmem 8 (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16921/131072 : ℝ)) (99198004657/100000000000 : ℝ) (991980046573/1000000000000 : ℝ) (251076146671/500000000000 : ℝ) (502152293351/1000000000000 : ℝ) (795156092703/1000000000000 : ℝ) (795156092721/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1401_exp_lower
  have heNumeric : (2054900901903/1000000000000 : ℝ)/4 ≤ Real.exp (-2664266949009/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900901903/1000000000000 : ℝ)/4 ≤ Real.exp ((2115/16384 : ℝ)-(795156092721/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2115/16384 : ℝ) (16921/131072 : ℝ) (795156092721/1000000000000 : ℝ) (2054900901903/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1402; no trusted numerical premise.
theorem cover8_leaf1402_exp_radius : (199596954740580503/200000000000000000 : ℝ) ≤ Real.exp ((-8461/524288 : ℝ)/8) ∧ Real.exp ((-8461/524288 : ℝ)/8) ≤ (249496193425725629/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8461/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1402_exp_lower : (920113419060510693/1000000000000000000 : ℝ) ≤ Real.exp ((-21314133747223/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314133747223/32000000000000 : ℝ)/8) ≤ (460056709530255347/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314133747223/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1402_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725255093/250000000000 : ℝ) ≤ 4*Real.exp (16921/131072 : ℝ)*Real.exp (-mu (radius 8 (8461/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725255093/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8461/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1402_exp_radius
  have hrNumeric : (491995722151/500000000000 : ℝ) ≤ Real.exp (-8461/524288 : ℝ) ∧ Real.exp (-8461/524288 : ℝ) ≤ (983991444303/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491995722151/500000000000 : ℝ) ≤ (radius 8 (8461/65536 : ℝ)) ∧ (radius 8 (8461/65536 : ℝ)) ≤ (983991444303/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8461/65536 : ℝ)) (491995722151/500000000000 : ℝ) (983991444303/1000000000000 : ℝ) (178215705083/1000000000000 : ℝ) (17821570509/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8461/65536 : ℝ)) (491995722151/500000000000 : ℝ) (983991444303/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491995722151/500000000000 : ℝ) (983991444303/1000000000000 : ℝ) (991995722151/1000000000000 : ℝ) (123999465269/125000000000 : ℝ) (991963428913/1000000000000 : ℝ) (198392685783/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 1 (991995722151/1000000000000 : ℝ) (123999465269/125000000000 : ℝ) (991963428913/1000000000000 : ℝ) (198392685783/200000000000 : ℝ) (247994893883/250000000000 : ℝ) (495989787767/500000000000 : ℝ) (4959897877/5000000000 : ℝ) (991979575403/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 2 (247994893883/250000000000 : ℝ) (495989787767/500000000000 : ℝ) (4959897877/5000000000 : ℝ) (991979575403/1000000000000 : ℝ) (495989787733/500000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 3 (495989787733/500000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 4 (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 5 (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 6 (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8461/65536 : ℝ)) 7 (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8461/65536 : ℝ))) (178215705083/1000000000000 : ℝ) (17821570509/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178215705083/1000000000000 : ℝ) (17821570509/100000000000 : ℝ) (589107852541/1000000000000 : ℝ) (117821570509/200000000000 : ℝ) (84431203967/200000000000 : ℝ) (105539004961/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 1 (589107852541/1000000000000 : ℝ) (117821570509/200000000000 : ℝ) (84431203967/200000000000 : ℝ) (105539004961/250000000000 : ℝ) (126407984047/250000000000 : ℝ) (101126387239/200000000000 : ℝ) (249346859957/500000000000 : ℝ) (249346859961/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 2 (126407984047/250000000000 : ℝ) (101126387239/200000000000 : ℝ) (249346859957/500000000000 : ℝ) (249346859961/500000000000 : ℝ) (502162828051/1000000000000 : ℝ) (502162828059/1000000000000 : ℝ) (50215084503/100000000000 : ℝ) (502150845039/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 3 (502162828051/1000000000000 : ℝ) (502162828059/1000000000000 : ℝ) (50215084503/100000000000 : ℝ) (502150845039/1000000000000 : ℝ) (25107841827/50000000000 : ℝ) (502156836549/1000000000000 : ℝ) (62769604563/125000000000 : ℝ) (251078418257/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 4 (25107841827/50000000000 : ℝ) (502156836549/1000000000000 : ℝ) (62769604563/125000000000 : ℝ) (251078418257/500000000000 : ℝ) (251078418261/500000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 5 (251078418261/500000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 6 (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8461/65536 : ℝ))) 7 (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8461/65536 : ℝ)) hmem 8 (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8461/65536 : ℝ))) hcmem 8 (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8461/65536 : ℝ)) (198395915093/200000000000 : ℝ) (991979575469/1000000000000 : ℝ) (502156836521/1000000000000 : ℝ) (125539209133/250000000000 : ℝ) (397581832221/500000000000 : ℝ) (49697729029/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1402_exp_lower
  have heNumeric : (513725255093/250000000000 : ℝ)/4 ≤ Real.exp (-21314133747223/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725255093/250000000000 : ℝ)/4 ≤ Real.exp ((16921/131072 : ℝ)-(49697729029/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16921/131072 : ℝ) (8461/65536 : ℝ) (49697729029/62500000000 : ℝ) (513725255093/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1403; no trusted numerical premise.
theorem cover8_leaf1403_exp_radius : (798387723787083/800000000000000 : ℝ) ≤ Real.exp ((-16923/1048576 : ℝ)/8) ∧ Real.exp ((-16923/1048576 : ℝ)/8) ≤ (997984654733853751/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16923/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1403_exp_lower : (920113425726793539/1000000000000000000 : ℝ) ≤ Real.exp ((-10657065946243/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657065946243/16000000000000 : ℝ)/8) ≤ (46005671286339677/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657065946243/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1403_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196045579/40000000000 : ℝ) ≤ 4*Real.exp (8461/65536 : ℝ)*Real.exp (-mu (radius 8 (16923/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (82196045579/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16923/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1403_exp_radius
  have hrNumeric : (196798101179/200000000000 : ℝ) ≤ Real.exp (-16923/1048576 : ℝ) ∧ Real.exp (-16923/1048576 : ℝ) ≤ (122998813237/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196798101179/200000000000 : ℝ) ≤ (radius 8 (16923/131072 : ℝ)) ∧ (radius 8 (16923/131072 : ℝ)) ≤ (122998813237/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16923/131072 : ℝ)) (196798101179/200000000000 : ℝ) (122998813237/125000000000 : ℝ) (4455522157/25000000000 : ℝ) (89110443143/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16923/131072 : ℝ)) (196798101179/200000000000 : ℝ) (122998813237/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196798101179/200000000000 : ℝ) (122998813237/125000000000 : ℝ) (991995252947/1000000000000 : ℝ) (247998813237/250000000000 : ℝ) (247990738977/250000000000 : ℝ) (99196295591/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 1 (991995252947/1000000000000 : ℝ) (247998813237/250000000000 : ℝ) (247990738977/250000000000 : ℝ) (99196295591/100000000000 : ℝ) (991979104427/1000000000000 : ℝ) (991979104429/1000000000000 : ℝ) (123997388037/125000000000 : ℝ) (495989552149/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 2 (991979104427/1000000000000 : ℝ) (991979104429/1000000000000 : ℝ) (123997388037/125000000000 : ℝ) (495989552149/500000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 3 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 4 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 5 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 6 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16923/131072 : ℝ)) 7 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16923/131072 : ℝ))) (4455522157/25000000000 : ℝ) (89110443143/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4455522157/25000000000 : ℝ) (89110443143/500000000000 : ℝ) (29455522157/50000000000 : ℝ) (589110443143/1000000000000 : ℝ) (21108107819/50000000000 : ℝ) (105540539097/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 1 (29455522157/50000000000 : ℝ) (589110443143/1000000000000 : ℝ) (21108107819/50000000000 : ℝ) (105540539097/250000000000 : ℝ) (6320453747/12500000000 : ℝ) (252818149883/500000000000 : ℝ) (249349220483/500000000000 : ℝ) (498698440973/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 2 (6320453747/12500000000 : ℝ) (252818149883/500000000000 : ℝ) (249349220483/500000000000 : ℝ) (498698440973/1000000000000 : ℝ) (502167370363/1000000000000 : ℝ) (50216737037/100000000000 : ℝ) (100431077737/200000000000 : ℝ) (502155388693/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 3 (502167370363/1000000000000 : ℝ) (50216737037/100000000000 : ℝ) (100431077737/200000000000 : ℝ) (502155388693/1000000000000 : ℝ) (125540344881/250000000000 : ℝ) (125540344883/250000000000 : ℝ) (15692543109/31250000000 : ℝ) (62770172437/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 4 (125540344881/250000000000 : ℝ) (125540344883/250000000000 : ℝ) (15692543109/31250000000 : ℝ) (62770172437/125000000000 : ℝ) (251080689753/500000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 5 (251080689753/500000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 6 (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16923/131072 : ℝ))) 7 (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16923/131072 : ℝ)) hmem 8 (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16923/131072 : ℝ))) hcmem 8 (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16923/131072 : ℝ)) (991979104361/1000000000000 : ℝ) (247994776091/250000000000 : ℝ) (100432275901/200000000000 : ℝ) (251080689757/500000000000 : ℝ) (19879280897/25000000000 : ℝ) (397585617949/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1403_exp_lower
  have heNumeric : (82196045579/40000000000 : ℝ)/4 ≤ Real.exp (-10657065946243/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196045579/40000000000 : ℝ)/4 ≤ Real.exp ((8461/65536 : ℝ)-(397585617949/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8461/65536 : ℝ) (16923/131072 : ℝ) (397585617949/500000000000 : ℝ) (82196045579/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1404; no trusted numerical premise.
theorem cover8_leaf1404_exp_radius : (31187016742650599/31250000000000000 : ℝ) ≤ Real.exp ((-4231/262144 : ℝ)/8) ∧ Real.exp ((-4231/262144 : ℝ)/8) ≤ (997984535764819169/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4231/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1404_exp_lower : (230028358106952679/250000000000000000 : ℝ) ≤ Real.exp ((-4262826005617/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262826005617/6400000000000 : ℝ)/8) ≤ (920113432427810717/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262826005617/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1404_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901259199/1000000000000 : ℝ) ≤ 4*Real.exp (16923/131072 : ℝ)*Real.exp (-mu (radius 8 (4231/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901259199/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4231/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1404_exp_radius
  have hrNumeric : (983989567489/1000000000000 : ℝ) ≤ Real.exp (-4231/262144 : ℝ) ∧ Real.exp (-4231/262144 : ℝ) ≤ (98398956749/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983989567489/1000000000000 : ℝ) ≤ (radius 8 (4231/32768 : ℝ)) ∧ (radius 8 (4231/32768 : ℝ)) ≤ (98398956749/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4231/32768 : ℝ)) (983989567489/1000000000000 : ℝ) (98398956749/100000000000 : ℝ) (35645213463/200000000000 : ℝ) (89113033661/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4231/32768 : ℝ)) (983989567489/1000000000000 : ℝ) (98398956749/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983989567489/1000000000000 : ℝ) (98398956749/100000000000 : ℝ) (484372453/488281250 : ℝ) (198398956749/200000000000 : ℝ) (991962482903/1000000000000 : ℝ) (198392496581/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 1 (484372453/488281250 : ℝ) (198398956749/200000000000 : ℝ) (991962482903/1000000000000 : ℝ) (198392496581/200000000000 : ℝ) (991978633323/1000000000000 : ℝ) (39679145333/40000000000 : ℝ) (123997329149/125000000000 : ℝ) (495989316597/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 2 (991978633323/1000000000000 : ℝ) (39679145333/40000000000 : ℝ) (123997329149/125000000000 : ℝ) (495989316597/500000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 3 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 4 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 5 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 6 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4231/32768 : ℝ)) 7 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4231/32768 : ℝ))) (35645213463/200000000000 : ℝ) (89113033661/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35645213463/200000000000 : ℝ) (89113033661/500000000000 : ℝ) (589113033657/1000000000000 : ℝ) (589113033661/1000000000000 : ℝ) (84433658529/200000000000 : ℝ) (211084146327/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 1 (589113033657/1000000000000 : ℝ) (589113033661/1000000000000 : ℝ) (84433658529/200000000000 : ℝ) (211084146327/500000000000 : ℝ) (505640663151/1000000000000 : ℝ) (252820331579/500000000000 : ℝ) (124675790451/250000000000 : ℝ) (124675790453/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 2 (505640663151/1000000000000 : ℝ) (252820331579/500000000000 : ℝ) (124675790451/250000000000 : ℝ) (124675790453/250000000000 : ℝ) (502171912477/1000000000000 : ℝ) (100434382497/200000000000 : ℝ) (502159932143/1000000000000 : ℝ) (502159932151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 3 (502171912477/1000000000000 : ℝ) (100434382497/200000000000 : ℝ) (502159932143/1000000000000 : ℝ) (502159932151/1000000000000 : ℝ) (50216592231/100000000000 : ℝ) (251082961159/500000000000 : ℝ) (251082961137/500000000000 : ℝ) (502165922283/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 4 (50216592231/100000000000 : ℝ) (251082961159/500000000000 : ℝ) (251082961137/500000000000 : ℝ) (502165922283/1000000000000 : ℝ) (125541480573/250000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 5 (125541480573/250000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 6 (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4231/32768 : ℝ))) 7 (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4231/32768 : ℝ)) hmem 8 (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4231/32768 : ℝ))) hcmem 8 (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4231/32768 : ℝ)) (991978633257/1000000000000 : ℝ) (49598931663/50000000000 : ℝ) (502165922291/1000000000000 : ℝ) (502165922301/1000000000000 : ℝ) (795178807011/1000000000000 : ℝ) (79517880703/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1404_exp_lower
  have heNumeric : (2054901259199/1000000000000 : ℝ)/4 ≤ Real.exp (-4262826005617/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901259199/1000000000000 : ℝ)/4 ≤ Real.exp ((16923/131072 : ℝ)-(79517880703/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16923/131072 : ℝ) (4231/32768 : ℝ) (79517880703/100000000000 : ℝ) (2054901259199/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1405; no trusted numerical premise.
theorem cover8_leaf1405_exp_radius : (62374026049737423/62500000000000000 : ℝ) ≤ Real.exp ((-16925/1048576 : ℝ)/8) ∧ Real.exp ((-16925/1048576 : ℝ)/8) ≤ (997984416795798769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16925/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1405_exp_lower : (920113439163907267/1000000000000000000 : ℝ) ≤ Real.exp ((-5328532038481/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328532038481/8000000000000 : ℝ)/8) ≤ (230028359790976817/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328532038481/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1405_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901379549/1000000000000 : ℝ) ≤ 4*Real.exp (4231/32768 : ℝ)*Real.exp (-mu (radius 8 (16925/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901379549/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16925/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1405_exp_radius
  have hrNumeric : (245997157271/250000000000 : ℝ) ≤ Real.exp (-16925/1048576 : ℝ) ∧ Real.exp (-16925/1048576 : ℝ) ≤ (196797725817/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245997157271/250000000000 : ℝ) ≤ (radius 8 (16925/131072 : ℝ)) ∧ (radius 8 (16925/131072 : ℝ)) ≤ (196797725817/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16925/131072 : ℝ)) (245997157271/250000000000 : ℝ) (196797725817/200000000000 : ℝ) (17823124819/100000000000 : ℝ) (44557812049/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16925/131072 : ℝ)) (245997157271/250000000000 : ℝ) (196797725817/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245997157271/250000000000 : ℝ) (196797725817/200000000000 : ℝ) (495997157271/500000000000 : ℝ) (991994314543/1000000000000 : ℝ) (991962009899/1000000000000 : ℝ) (991962009901/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 1 (495997157271/500000000000 : ℝ) (991994314543/1000000000000 : ℝ) (991962009899/1000000000000 : ℝ) (991962009901/1000000000000 : ℝ) (49598908111/50000000000 : ℝ) (495989081111/500000000000 : ℝ) (123997270261/125000000000 : ℝ) (991978162091/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 2 (49598908111/50000000000 : ℝ) (495989081111/500000000000 : ℝ) (123997270261/125000000000 : ℝ) (991978162091/1000000000000 : ℝ) (495989081077/500000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 3 (495989081077/500000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 4 (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 5 (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 6 (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16925/131072 : ℝ)) 7 (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16925/131072 : ℝ))) (17823124819/100000000000 : ℝ) (44557812049/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17823124819/100000000000 : ℝ) (44557812049/250000000000 : ℝ) (117823124819/200000000000 : ℝ) (294557812049/500000000000 : ℝ) (422174428631/1000000000000 : ℝ) (422174428639/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 1 (117823124819/200000000000 : ℝ) (294557812049/500000000000 : ℝ) (422174428631/1000000000000 : ℝ) (422174428639/1000000000000 : ℝ) (505645026363/1000000000000 : ℝ) (505645026369/1000000000000 : ℝ) (7792310663/15625000000 : ℝ) (498707882439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 2 (505645026363/1000000000000 : ℝ) (505645026369/1000000000000 : ℝ) (7792310663/15625000000 : ℝ) (498707882439/1000000000000 : ℝ) (502176454397/1000000000000 : ℝ) (125544113601/250000000000 : ℝ) (100432895081/200000000000 : ℝ) (502164475413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 3 (502176454397/1000000000000 : ℝ) (125544113601/250000000000 : ℝ) (100432895081/200000000000 : ℝ) (502164475413/1000000000000 : ℝ) (502170464901/1000000000000 : ℝ) (502170464909/1000000000000 : ℝ) (100434092973/200000000000 : ℝ) (502170464873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 4 (502170464901/1000000000000 : ℝ) (502170464909/1000000000000 : ℝ) (100434092973/200000000000 : ℝ) (502170464873/1000000000000 : ℝ) (502170464883/1000000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 5 (502170464883/1000000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 6 (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16925/131072 : ℝ))) 7 (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16925/131072 : ℝ)) hmem 8 (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16925/131072 : ℝ))) hcmem 8 (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16925/131072 : ℝ)) (991978162153/1000000000000 : ℝ) (991978162157/1000000000000 : ℝ) (251085232441/500000000000 : ℝ) (502170464891/1000000000000 : ℝ) (795186377839/1000000000000 : ℝ) (795186377857/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1405_exp_lower
  have heNumeric : (2054901379549/1000000000000 : ℝ)/4 ≤ Real.exp (-5328532038481/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901379549/1000000000000 : ℝ)/4 ≤ Real.exp ((4231/32768 : ℝ)-(795186377857/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4231/32768 : ℝ) (16925/131072 : ℝ) (795186377857/1000000000000 : ℝ) (2054901379549/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1406; no trusted numerical premise.
theorem cover8_leaf1406_exp_radius : (19959685956535851/20000000000000000 : ℝ) ≤ Real.exp ((-8463/524288 : ℝ)/8) ∧ Real.exp ((-8463/524288 : ℝ)/8) ≤ (997984297826792551/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8463/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1406_exp_lower : (184022689186924627/200000000000000000 : ℝ) ≤ Real.exp ((-21314126270131/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314126270131/32000000000000 : ℝ)/8) ≤ (28753545185456973/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314126270131/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1406_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450750259/500000000000 : ℝ) ≤ 4*Real.exp (16925/131072 : ℝ)*Real.exp (-mu (radius 8 (8463/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450750259/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8463/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1406_exp_radius
  have hrNumeric : (24599692267/25000000000 : ℝ) ≤ Real.exp (-8463/524288 : ℝ) ∧ Real.exp (-8463/524288 : ℝ) ≤ (983987690681/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24599692267/25000000000 : ℝ) ≤ (radius 8 (8463/65536 : ℝ)) ∧ (radius 8 (8463/65536 : ℝ)) ≤ (983987690681/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8463/65536 : ℝ)) (24599692267/25000000000 : ℝ) (983987690681/1000000000000 : ℝ) (178236428903/1000000000000 : ℝ) (17823642891/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8463/65536 : ℝ)) (24599692267/25000000000 : ℝ) (983987690681/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24599692267/25000000000 : ℝ) (983987690681/1000000000000 : ℝ) (49599692267/50000000000 : ℝ) (991993845341/1000000000000 : ℝ) (198392307379/200000000000 : ℝ) (7749699507/7812500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 1 (49599692267/50000000000 : ℝ) (991993845341/1000000000000 : ℝ) (198392307379/200000000000 : ℝ) (7749699507/7812500000 : ℝ) (991977691117/1000000000000 : ℝ) (991977691119/1000000000000 : ℝ) (198395538197/200000000000 : ℝ) (991977690987/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 2 (991977691117/1000000000000 : ℝ) (991977691119/1000000000000 : ℝ) (198395538197/200000000000 : ℝ) (991977690987/1000000000000 : ℝ) (991977691051/1000000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 3 (991977691051/1000000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 4 (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 5 (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 6 (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8463/65536 : ℝ)) 7 (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8463/65536 : ℝ))) (178236428903/1000000000000 : ℝ) (17823642891/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178236428903/1000000000000 : ℝ) (17823642891/100000000000 : ℝ) (589118214451/1000000000000 : ℝ) (117823642891/200000000000 : ℝ) (84436112867/200000000000 : ℝ) (84436112869/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 1 (589118214451/1000000000000 : ℝ) (117823642891/200000000000 : ℝ) (84436112867/200000000000 : ℝ) (84436112869/200000000000 : ℝ) (505649389393/1000000000000 : ℝ) (2528246947/5000000000 : ℝ) (99742520569/200000000000 : ℝ) (249356301427/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 2 (505649389393/1000000000000 : ℝ) (2528246947/5000000000 : ℝ) (99742520569/200000000000 : ℝ) (249356301427/500000000000 : ℝ) (502180996119/1000000000000 : ℝ) (502180996127/1000000000000 : ℝ) (50216901847/100000000000 : ℝ) (502169018479/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 3 (502180996119/1000000000000 : ℝ) (502180996127/1000000000000 : ℝ) (50216901847/100000000000 : ℝ) (502169018479/1000000000000 : ℝ) (251087503647/500000000000 : ℝ) (502175007303/1000000000000 : ℝ) (251087503629/500000000000 : ℝ) (125543751817/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 4 (251087503647/500000000000 : ℝ) (502175007303/1000000000000 : ℝ) (251087503629/500000000000 : ℝ) (125543751817/250000000000 : ℝ) (125543751819/250000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 5 (125543751819/250000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 6 (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8463/65536 : ℝ))) 7 (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8463/65536 : ℝ)) hmem 8 (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8463/65536 : ℝ))) hcmem 8 (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8463/65536 : ℝ)) (19839553821/20000000000 : ℝ) (991977691053/1000000000000 : ℝ) (20087000291/40000000000 : ℝ) (251087503643/500000000000 : ℝ) (397596974181/500000000000 : ℝ) (795193948383/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1406_exp_lower
  have heNumeric : (1027450750259/500000000000 : ℝ)/4 ≤ Real.exp (-21314126270131/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450750259/500000000000 : ℝ)/4 ≤ Real.exp ((16925/131072 : ℝ)-(795193948383/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16925/131072 : ℝ) (8463/65536 : ℝ) (795193948383/1000000000000 : ℝ) (1027450750259/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1407; no trusted numerical premise.
theorem cover8_leaf1407_exp_radius : (498992089428900257/500000000000000000 : ℝ) ≤ Real.exp ((-16927/1048576 : ℝ)/8) ∧ Real.exp ((-16927/1048576 : ℝ)/8) ≤ (199596835771560103/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16927/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1407_exp_lower : (460056726369979161/500000000000000000 : ℝ) ≤ Real.exp ((-10657062188353/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062188353/16000000000000 : ℝ)/8) ≤ (920113452739958323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062188353/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1407_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450811053/500000000000 : ℝ) ≤ 4*Real.exp (8463/65536 : ℝ)*Real.exp (-mu (radius 8 (16927/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450811053/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16927/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1407_exp_radius
  have hrNumeric : (245996688069/250000000000 : ℝ) ≤ Real.exp (-16927/1048576 : ℝ) ∧ Real.exp (-16927/1048576 : ℝ) ≤ (983986752277/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245996688069/250000000000 : ℝ) ≤ (radius 8 (16927/131072 : ℝ)) ∧ (radius 8 (16927/131072 : ℝ)) ≤ (983986752277/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16927/131072 : ℝ)) (245996688069/250000000000 : ℝ) (983986752277/1000000000000 : ℝ) (178241609461/1000000000000 : ℝ) (178241609467/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16927/131072 : ℝ)) (245996688069/250000000000 : ℝ) (983986752277/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245996688069/250000000000 : ℝ) (983986752277/1000000000000 : ℝ) (495996688069/500000000000 : ℝ) (991993376139/1000000000000 : ℝ) (991961063891/1000000000000 : ℝ) (247990265973/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 1 (495996688069/500000000000 : ℝ) (991993376139/1000000000000 : ℝ) (991961063891/1000000000000 : ℝ) (247990265973/250000000000 : ℝ) (495988610007/500000000000 : ℝ) (61998576251/62500000000 : ℝ) (495988609941/500000000000 : ℝ) (247994304971/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 2 (495988610007/500000000000 : ℝ) (61998576251/62500000000 : ℝ) (495988609941/500000000000 : ℝ) (247994304971/250000000000 : ℝ) (247994304987/250000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 3 (247994304987/250000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 4 (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 5 (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 6 (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16927/131072 : ℝ)) 7 (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16927/131072 : ℝ))) (178241609461/1000000000000 : ℝ) (178241609467/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178241609461/1000000000000 : ℝ) (178241609467/1000000000000 : ℝ) (58912080473/100000000000 : ℝ) (294560402367/500000000000 : ℝ) (52773337471/125000000000 : ℝ) (412291699/976562500 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 1 (58912080473/100000000000 : ℝ) (294560402367/500000000000 : ℝ) (52773337471/125000000000 : ℝ) (412291699/976562500 : ℝ) (505653752249/1000000000000 : ℝ) (101130750451/200000000000 : ℝ) (498717323053/1000000000000 : ℝ) (24935866153/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 2 (505653752249/1000000000000 : ℝ) (101130750451/200000000000 : ℝ) (498717323053/1000000000000 : ℝ) (24935866153/50000000000 : ℝ) (502185537651/1000000000000 : ℝ) (251092768829/500000000000 : ℝ) (980807737/1953125000 : ℝ) (502173561351/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 3 (502185537651/1000000000000 : ℝ) (251092768829/500000000000 : ℝ) (980807737/1953125000 : ℝ) (502173561351/1000000000000 : ℝ) (502179549497/1000000000000 : ℝ) (100435909901/200000000000 : ℝ) (502179549461/1000000000000 : ℝ) (502179549469/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 4 (502179549497/1000000000000 : ℝ) (100435909901/200000000000 : ℝ) (502179549461/1000000000000 : ℝ) (502179549469/1000000000000 : ℝ) (502179549479/1000000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 5 (502179549479/1000000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 6 (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16927/131072 : ℝ))) 7 (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16927/131072 : ℝ)) hmem 8 (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16927/131072 : ℝ))) hcmem 8 (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16927/131072 : ℝ)) (991977219947/1000000000000 : ℝ) (19839544399/20000000000 : ℝ) (251089774739/500000000000 : ℝ) (502179549487/1000000000000 : ℝ) (79520151859/100000000000 : ℝ) (49700094913/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1407_exp_lower
  have heNumeric : (1027450811053/500000000000 : ℝ)/4 ≤ Real.exp (-10657062188353/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450811053/500000000000 : ℝ)/4 ≤ Real.exp ((8463/65536 : ℝ)-(49700094913/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8463/65536 : ℝ) (16927/131072 : ℝ) (49700094913/62500000000 : ℝ) (1027450811053/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1408; no trusted numerical premise.
theorem cover8_leaf1408_exp_radius : (997984059888822661/1000000000000000000 : ℝ) ≤ Real.exp ((-529/32768 : ℝ)/8) ∧ Real.exp ((-529/32768 : ℝ)/8) ≤ (498992029944411331/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-529/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1408_exp_lower : (920113459580602913/1000000000000000000 : ℝ) ≤ Real.exp ((-21314122473457/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122473457/32000000000000 : ℝ)/8) ≤ (460056729790301457/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122473457/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1408_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725436081/250000000000 : ℝ) ≤ 4*Real.exp (16927/131072 : ℝ)*Real.exp (-mu (radius 8 (529/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (513725436081/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (529/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1408_exp_radius
  have hrNumeric : (491992906937/500000000000 : ℝ) ≤ Real.exp (-529/32768 : ℝ) ∧ Real.exp (-529/32768 : ℝ) ≤ (7871886511/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491992906937/500000000000 : ℝ) ≤ (radius 8 (529/4096 : ℝ)) ∧ (radius 8 (529/4096 : ℝ)) ≤ (7871886511/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (529/4096 : ℝ)) (491992906937/500000000000 : ℝ) (7871886511/8000000000 : ℝ) (44561697463/250000000000 : ℝ) (178246789859/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (529/4096 : ℝ)) (491992906937/500000000000 : ℝ) (7871886511/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (529/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491992906937/500000000000 : ℝ) (7871886511/8000000000 : ℝ) (991992906937/1000000000000 : ℝ) (495996453469/500000000000 : ℝ) (991960590887/1000000000000 : ℝ) (991960590889/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (529/4096 : ℝ)) 1 (991992906937/1000000000000 : ℝ) (495996453469/500000000000 : ℝ) (991960590887/1000000000000 : ℝ) (991960590889/1000000000000 : ℝ) (61998546807/62500000000 : ℝ) (495988374457/500000000000 : ℝ) (49598837439/50000000000 : ℝ) (495988374391/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (529/4096 : ℝ)) 2 (61998546807/62500000000 : ℝ) (495988374457/500000000000 : ℝ) (49598837439/50000000000 : ℝ) (495988374391/500000000000 : ℝ) (495988374423/500000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (529/4096 : ℝ)) 3 (495988374423/500000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (529/4096 : ℝ)) 4 (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (529/4096 : ℝ)) 5 (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (529/4096 : ℝ)) 6 (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (529/4096 : ℝ)) 7 (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (529/4096 : ℝ))) (44561697463/250000000000 : ℝ) (178246789859/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44561697463/250000000000 : ℝ) (178246789859/1000000000000 : ℝ) (294561697463/500000000000 : ℝ) (58912339493/100000000000 : ℝ) (422192834913/1000000000000 : ℝ) (211096417461/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 1 (294561697463/500000000000 : ℝ) (58912339493/100000000000 : ℝ) (422192834913/1000000000000 : ℝ) (211096417461/500000000000 : ℝ) (505658114919/1000000000000 : ℝ) (252829057463/500000000000 : ℝ) (498722043043/1000000000000 : ℝ) (498722043051/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 2 (505658114919/1000000000000 : ℝ) (252829057463/500000000000 : ℝ) (498722043043/1000000000000 : ℝ) (498722043051/1000000000000 : ℝ) (502190078981/1000000000000 : ℝ) (502190078989/1000000000000 : ℝ) (31386131501/62500000000 : ℝ) (20087124161/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 3 (502190078981/1000000000000 : ℝ) (502190078989/1000000000000 : ℝ) (31386131501/62500000000 : ℝ) (20087124161/40000000000 : ℝ) (251092045749/500000000000 : ℝ) (502184091507/1000000000000 : ℝ) (251092045731/500000000000 : ℝ) (31386505717/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 4 (251092045749/500000000000 : ℝ) (502184091507/1000000000000 : ℝ) (251092045731/500000000000 : ℝ) (31386505717/62500000000 : ℝ) (12554602287/25000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 5 (12554602287/25000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 6 (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (529/4096 : ℝ))) 7 (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (529/4096 : ℝ)) hmem 8 (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (529/4096 : ℝ))) hcmem 8 (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (529/4096 : ℝ)) (198395349769/200000000000 : ℝ) (61998546803/62500000000 : ℝ) (502184091479/1000000000000 : ℝ) (50218409149/100000000000 : ℝ) (159041817701/200000000000 : ℝ) (397604544263/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1408_exp_lower
  have heNumeric : (513725436081/250000000000 : ℝ)/4 ≤ Real.exp (-21314122473457/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725436081/250000000000 : ℝ)/4 ≤ Real.exp ((16927/131072 : ℝ)-(397604544263/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16927/131072 : ℝ) (529/4096 : ℝ) (397604544263/500000000000 : ℝ) (513725436081/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1409; no trusted numerical premise.
theorem cover8_leaf1409_exp_radius : (99798394091985899/100000000000000000 : ℝ) ≤ Real.exp ((-16929/1048576 : ℝ)/8) ∧ Real.exp ((-16929/1048576 : ℝ)/8) ≤ (997983940919858991/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16929/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1409_exp_lower : (230028366613909199/250000000000000000 : ℝ) ≤ Real.exp ((-1040728543/1562500000 : ℝ)/8) ∧ Real.exp ((-1040728543/1562500000 : ℝ)/8) ≤ (920113466455636797/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1040728543/1562500000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1409_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901867157/1000000000000 : ℝ) ≤ 4*Real.exp (529/4096 : ℝ)*Real.exp (-mu (radius 8 (16929/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901867157/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16929/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1409_exp_radius
  have hrNumeric : (61499054717/62500000000 : ℝ) ≤ Real.exp (-16929/1048576 : ℝ) ∧ Real.exp (-16929/1048576 : ℝ) ≤ (983984875473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61499054717/62500000000 : ℝ) ≤ (radius 8 (16929/131072 : ℝ)) ∧ (radius 8 (16929/131072 : ℝ)) ≤ (983984875473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16929/131072 : ℝ)) (61499054717/62500000000 : ℝ) (983984875473/1000000000000 : ℝ) (22281496261/125000000000 : ℝ) (89125985047/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16929/131072 : ℝ)) (61499054717/62500000000 : ℝ) (983984875473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61499054717/62500000000 : ℝ) (983984875473/1000000000000 : ℝ) (123999054717/125000000000 : ℝ) (991992437737/1000000000000 : ℝ) (991960117883/1000000000000 : ℝ) (198392023577/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 1 (123999054717/125000000000 : ℝ) (991992437737/1000000000000 : ℝ) (991960117883/1000000000000 : ℝ) (198392023577/200000000000 : ℝ) (991976277809/1000000000000 : ℝ) (991976277811/1000000000000 : ℝ) (991976277677/1000000000000 : ℝ) (12399703471/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 2 (991976277809/1000000000000 : ℝ) (991976277811/1000000000000 : ℝ) (991976277677/1000000000000 : ℝ) (12399703471/12500000000 : ℝ) (991976277743/1000000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 3 (991976277743/1000000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 4 (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 5 (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 6 (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16929/131072 : ℝ)) 7 (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16929/131072 : ℝ))) (22281496261/125000000000 : ℝ) (89125985047/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22281496261/125000000000 : ℝ) (89125985047/500000000000 : ℝ) (147281496261/250000000000 : ℝ) (589125985047/1000000000000 : ℝ) (84439793957/200000000000 : ℝ) (422198969793/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 1 (147281496261/250000000000 : ℝ) (589125985047/1000000000000 : ℝ) (84439793957/200000000000 : ℝ) (422198969793/1000000000000 : ℝ) (252831238707/500000000000 : ℝ) (25283123871/50000000000 : ℝ) (249363381413/500000000000 : ℝ) (498726762833/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 2 (252831238707/500000000000 : ℝ) (25283123871/50000000000 : ℝ) (249363381413/500000000000 : ℝ) (498726762833/1000000000000 : ℝ) (12554865503/25000000000 : ℝ) (502194620127/1000000000000 : ℝ) (502182646497/1000000000000 : ℝ) (100436529301/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 3 (12554865503/25000000000 : ℝ) (502194620127/1000000000000 : ℝ) (502182646497/1000000000000 : ℝ) (100436529301/200000000000 : ℝ) (125547158327/250000000000 : ℝ) (125547158329/250000000000 : ℝ) (62773579159/125000000000 : ℝ) (502188633281/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 4 (125547158327/250000000000 : ℝ) (125547158329/250000000000 : ℝ) (62773579159/125000000000 : ℝ) (502188633281/1000000000000 : ℝ) (50218863329/100000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 5 (50218863329/100000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 6 (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16929/131072 : ℝ))) 7 (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16929/131072 : ℝ)) hmem 8 (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16929/131072 : ℝ))) hcmem 8 (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16929/131072 : ℝ)) (495988138871/500000000000 : ℝ) (495988138873/500000000000 : ℝ) (502188633289/1000000000000 : ℝ) (502188633299/1000000000000 : ℝ) (1272346653/1600000000 : ℝ) (159043331629/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1409_exp_lower
  have heNumeric : (2054901867157/1000000000000 : ℝ)/4 ≤ Real.exp (-1040728543/1562500000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901867157/1000000000000 : ℝ)/4 ≤ Real.exp ((529/4096 : ℝ)-(159043331629/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (529/4096 : ℝ) (16929/131072 : ℝ) (159043331629/200000000000 : ℝ) (2054901867157/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1410; no trusted numerical premise.
theorem cover8_leaf1410_exp_radius : (997983821950909501/1000000000000000000 : ℝ) ≤ Real.exp ((-8465/524288 : ℝ)/8) ∧ Real.exp ((-8465/524288 : ℝ)/8) ≤ (498991910975454751/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8465/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1410_exp_lower : (184022694673311031/200000000000000000 : ℝ) ≤ Real.exp ((-21314118637839/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314118637839/32000000000000 : ℝ)/8) ≤ (230028368341638789/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314118637839/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1410_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901990631/1000000000000 : ℝ) ≤ 4*Real.exp (16929/131072 : ℝ)*Real.exp (-mu (radius 8 (8465/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901990631/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8465/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1410_exp_radius
  have hrNumeric : (61498996067/62500000000 : ℝ) ≤ Real.exp (-8465/524288 : ℝ) ∧ Real.exp (-8465/524288 : ℝ) ≤ (983983937073/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61498996067/62500000000 : ℝ) ≤ (radius 8 (8465/65536 : ℝ)) ∧ (radius 8 (8465/65536 : ℝ)) ≤ (983983937073/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8465/65536 : ℝ)) (61498996067/62500000000 : ℝ) (983983937073/1000000000000 : ℝ) (178257150157/1000000000000 : ℝ) (44564287541/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8465/65536 : ℝ)) (61498996067/62500000000 : ℝ) (983983937073/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61498996067/62500000000 : ℝ) (983983937073/1000000000000 : ℝ) (123998996067/125000000000 : ℝ) (991991968537/1000000000000 : ℝ) (12399495561/12500000000 : ℝ) (495979822441/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 1 (123998996067/125000000000 : ℝ) (991991968537/1000000000000 : ℝ) (12399495561/12500000000 : ℝ) (495979822441/500000000000 : ℝ) (247993951677/250000000000 : ℝ) (99197580671/100000000000 : ℝ) (61998487911/62500000000 : ℝ) (495987903289/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 2 (247993951677/250000000000 : ℝ) (99197580671/100000000000 : ℝ) (61998487911/62500000000 : ℝ) (495987903289/500000000000 : ℝ) (495987903321/500000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 3 (495987903321/500000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 4 (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 5 (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 6 (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8465/65536 : ℝ)) 7 (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8465/65536 : ℝ))) (178257150157/1000000000000 : ℝ) (44564287541/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178257150157/1000000000000 : ℝ) (44564287541/250000000000 : ℝ) (294564287539/500000000000 : ℝ) (294564287541/500000000000 : ℝ) (422205104371/1000000000000 : ℝ) (21110255219/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 1 (294564287539/500000000000 : ℝ) (294564287541/500000000000 : ℝ) (422205104371/1000000000000 : ℝ) (21110255219/50000000000 : ℝ) (126416709931/250000000000 : ℝ) (505666839731/1000000000000 : ℝ) (498731482391/1000000000000 : ℝ) (498731482399/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 2 (126416709931/250000000000 : ℝ) (505666839731/1000000000000 : ℝ) (498731482391/1000000000000 : ℝ) (498731482399/1000000000000 : ℝ) (502199161057/1000000000000 : ℝ) (100439832213/200000000000 : ℝ) (62773398597/125000000000 : ℝ) (100437437757/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 3 (502199161057/1000000000000 : ℝ) (100439832213/200000000000 : ℝ) (62773398597/125000000000 : ℝ) (100437437757/200000000000 : ℝ) (125548293729/250000000000 : ℝ) (20087726997/40000000000 : ℝ) (3138707343/6250000000 : ℝ) (50219317489/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 4 (125548293729/250000000000 : ℝ) (20087726997/40000000000 : ℝ) (3138707343/6250000000 : ℝ) (50219317489/100000000000 : ℝ) (251096587449/500000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 5 (251096587449/500000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 6 (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8465/65536 : ℝ))) 7 (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8465/65536 : ℝ)) hmem 8 (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8465/65536 : ℝ))) hcmem 8 (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8465/65536 : ℝ)) (991975806641/1000000000000 : ℝ) (247993951661/250000000000 : ℝ) (502193174897/1000000000000 : ℝ) (125548293727/250000000000 : ℝ) (795224227431/1000000000000 : ℝ) (198806056863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1410_exp_lower
  have heNumeric : (2054901990631/1000000000000 : ℝ)/4 ≤ Real.exp (-21314118637839/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901990631/1000000000000 : ℝ)/4 ≤ Real.exp ((16929/131072 : ℝ)-(198806056863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16929/131072 : ℝ) (8465/65536 : ℝ) (198806056863/250000000000 : ℝ) (2054901990631/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1411; no trusted numerical premise.
theorem cover8_leaf1411_exp_radius : (498991851490987097/500000000000000000 : ℝ) ≤ Real.exp ((-16931/1048576 : ℝ)/8) ∧ Real.exp ((-16931/1048576 : ℝ)/8) ≤ (199596740596394839/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16931/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1411_exp_lower : (920113480311402751/1000000000000000000 : ℝ) ≤ Real.exp ((-10657058352799/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657058352799/16000000000000 : ℝ)/8) ≤ (3594193282466417/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657058352799/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1411_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902114711/1000000000000 : ℝ) ≤ 4*Real.exp (8465/65536 : ℝ)*Real.exp (-mu (radius 8 (16931/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902114711/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16931/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1411_exp_radius
  have hrNumeric : (61498937417/62500000000 : ℝ) ≤ Real.exp (-16931/1048576 : ℝ) ∧ Real.exp (-16931/1048576 : ℝ) ≤ (983982998673/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61498937417/62500000000 : ℝ) ≤ (radius 8 (16931/131072 : ℝ)) ∧ (radius 8 (16931/131072 : ℝ)) ≤ (983982998673/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16931/131072 : ℝ)) (61498937417/62500000000 : ℝ) (983982998673/1000000000000 : ℝ) (178262330071/1000000000000 : ℝ) (178262330077/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16931/131072 : ℝ)) (61498937417/62500000000 : ℝ) (983982998673/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61498937417/62500000000 : ℝ) (983982998673/1000000000000 : ℝ) (123998937417/125000000000 : ℝ) (991991499337/1000000000000 : ℝ) (991959171877/1000000000000 : ℝ) (991959171879/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 1 (123998937417/125000000000 : ℝ) (991991499337/1000000000000 : ℝ) (991959171877/1000000000000 : ℝ) (991959171879/1000000000000 : ℝ) (495987667803/500000000000 : ℝ) (123996916951/125000000000 : ℝ) (495987667737/500000000000 : ℝ) (991975335477/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 2 (495987667803/500000000000 : ℝ) (123996916951/125000000000 : ℝ) (495987667737/500000000000 : ℝ) (991975335477/1000000000000 : ℝ) (49598766777/50000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 3 (49598766777/50000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 4 (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 5 (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 6 (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16931/131072 : ℝ)) 7 (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16931/131072 : ℝ))) (178262330071/1000000000000 : ℝ) (178262330077/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178262330071/1000000000000 : ℝ) (178262330077/1000000000000 : ℝ) (117826233007/200000000000 : ℝ) (589131165039/1000000000000 : ℝ) (422211238683/1000000000000 : ℝ) (105552809673/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 1 (117826233007/200000000000 : ℝ) (589131165039/1000000000000 : ℝ) (422211238683/1000000000000 : ℝ) (105552809673/250000000000 : ℝ) (505671201859/1000000000000 : ℝ) (252835600933/500000000000 : ℝ) (1994944807/4000000000 : ℝ) (249368100879/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 2 (505671201859/1000000000000 : ℝ) (252835600933/500000000000 : ℝ) (1994944807/4000000000 : ℝ) (249368100879/500000000000 : ℝ) (125550925451/250000000000 : ℝ) (125550925453/250000000000 : ℝ) (100438346173/200000000000 : ℝ) (502191730873/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 3 (125550925451/250000000000 : ℝ) (125550925453/250000000000 : ℝ) (100438346173/200000000000 : ℝ) (502191730873/1000000000000 : ℝ) (251098858167/500000000000 : ℝ) (502197716343/1000000000000 : ℝ) (251098858149/500000000000 : ℝ) (502197716307/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 4 (251098858167/500000000000 : ℝ) (502197716343/1000000000000 : ℝ) (251098858149/500000000000 : ℝ) (502197716307/1000000000000 : ℝ) (125549429079/250000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 5 (125549429079/250000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 6 (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16931/131072 : ℝ))) 7 (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16931/131072 : ℝ)) hmem 8 (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16931/131072 : ℝ))) hcmem 8 (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16931/131072 : ℝ)) (991975335539/1000000000000 : ℝ) (991975335543/1000000000000 : ℝ) (100439543263/200000000000 : ℝ) (20087908653/40000000000 : ℝ) (198807949111/250000000000 : ℝ) (49701987279/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1411_exp_lower
  have heNumeric : (2054902114711/1000000000000 : ℝ)/4 ≤ Real.exp (-10657058352799/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902114711/1000000000000 : ℝ)/4 ≤ Real.exp ((8465/65536 : ℝ)-(49701987279/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8465/65536 : ℝ) (16931/131072 : ℝ) (49701987279/62500000000 : ℝ) (2054902114711/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1412; no trusted numerical premise.
theorem cover8_leaf1412_exp_radius : (997983584013053069/1000000000000000000 : ℝ) ≤ Real.exp ((-4233/262144 : ℝ)/8) ∧ Real.exp ((-4233/262144 : ℝ)/8) ≤ (99798358401305307/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4233/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1412_exp_lower : (115014185911401839/125000000000000000 : ℝ) ≤ Real.exp ((-21314114763629/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314114763629/32000000000000 : ℝ)/8) ≤ (920113487291214713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314114763629/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1412_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862779927/125000000000 : ℝ) ≤ 4*Real.exp (16931/131072 : ℝ)*Real.exp (-mu (radius 8 (4233/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256862779927/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4233/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1412_exp_radius
  have hrNumeric : (983982060273/1000000000000 : ℝ) ≤ Real.exp (-4233/262144 : ℝ) ∧ Real.exp (-4233/262144 : ℝ) ≤ (491991030137/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983982060273/1000000000000 : ℝ) ≤ (radius 8 (4233/32768 : ℝ)) ∧ (radius 8 (4233/32768 : ℝ)) ≤ (491991030137/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4233/32768 : ℝ)) (983982060273/1000000000000 : ℝ) (491991030137/500000000000 : ℝ) (2785429841/15625000000 : ℝ) (17826750983/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4233/32768 : ℝ)) (983982060273/1000000000000 : ℝ) (491991030137/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983982060273/1000000000000 : ℝ) (491991030137/500000000000 : ℝ) (123998878767/125000000000 : ℝ) (991991030137/1000000000000 : ℝ) (495979349437/500000000000 : ℝ) (247989674719/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 1 (123998878767/125000000000 : ℝ) (991991030137/1000000000000 : ℝ) (495979349437/500000000000 : ℝ) (247989674719/250000000000 : ℝ) (198394972901/200000000000 : ℝ) (991974864507/1000000000000 : ℝ) (991974864373/1000000000000 : ℝ) (1587159783/1600000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 2 (198394972901/200000000000 : ℝ) (991974864507/1000000000000 : ℝ) (991974864373/1000000000000 : ℝ) (1587159783/1600000000 : ℝ) (991974864439/1000000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 3 (991974864439/1000000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 4 (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 5 (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 6 (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4233/32768 : ℝ)) 7 (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4233/32768 : ℝ))) (2785429841/15625000000 : ℝ) (17826750983/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2785429841/15625000000 : ℝ) (17826750983/100000000000 : ℝ) (18410429841/31250000000 : ℝ) (117826750983/200000000000 : ℝ) (105554343179/250000000000 : ℝ) (16888694909/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 1 (18410429841/31250000000 : ℝ) (117826750983/200000000000 : ℝ) (105554343179/250000000000 : ℝ) (16888694909/40000000000 : ℝ) (252837781907/500000000000 : ℝ) (25283778191/50000000000 : ℝ) (498740920897/1000000000000 : ℝ) (62342615113/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 2 (252837781907/500000000000 : ℝ) (25283778191/50000000000 : ℝ) (498740920897/1000000000000 : ℝ) (62342615113/125000000000 : ℝ) (100441648471/200000000000 : ℝ) (251104121181/500000000000 : ℝ) (502196272757/1000000000000 : ℝ) (100439254553/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 3 (100441648471/200000000000 : ℝ) (251104121181/500000000000 : ℝ) (502196272757/1000000000000 : ℝ) (100439254553/200000000000 : ℝ) (125550564389/250000000000 : ℝ) (125550564391/250000000000 : ℝ) (6277528219/12500000000 : ℝ) (62775282191/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 4 (125550564389/250000000000 : ℝ) (125550564391/250000000000 : ℝ) (6277528219/12500000000 : ℝ) (62775282191/125000000000 : ℝ) (251101128769/500000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 5 (251101128769/500000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 6 (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4233/32768 : ℝ))) 7 (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4233/32768 : ℝ)) hmem 8 (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4233/32768 : ℝ))) hcmem 8 (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4233/32768 : ℝ)) (495987432219/500000000000 : ℝ) (991974864441/1000000000000 : ℝ) (502202257537/1000000000000 : ℝ) (251101128773/500000000000 : ℝ) (397619682577/500000000000 : ℝ) (198809841293/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1412_exp_lower
  have heNumeric : (256862779927/125000000000 : ℝ)/4 ≤ Real.exp (-21314114763629/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862779927/125000000000 : ℝ)/4 ≤ Real.exp ((16931/131072 : ℝ)-(198809841293/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16931/131072 : ℝ) (4233/32768 : ℝ) (198809841293/250000000000 : ℝ) (256862779927/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1413; no trusted numerical premise.
theorem cover8_leaf1413_exp_radius : (997983465044146127/1000000000000000000 : ℝ) ≤ Real.exp ((-16933/1048576 : ℝ)/8) ∧ Real.exp ((-16933/1048576 : ℝ)/8) ≤ (62373966565259133/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16933/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1413_exp_lower : (920113494305761011/1000000000000000000 : ℝ) ≤ Real.exp ((-5328528202999/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328528202999/8000000000000 : ℝ)/8) ≤ (230028373576440253/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328528202999/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1413_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902364741/1000000000000 : ℝ) ≤ 4*Real.exp (4233/32768 : ℝ)*Real.exp (-mu (radius 8 (16933/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902364741/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16933/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1413_exp_radius
  have hrNumeric : (314873959/320000000 : ℝ) ≤ Real.exp (-16933/1048576 : ℝ) ∧ Real.exp (-16933/1048576 : ℝ) ≤ (245995280469/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (314873959/320000000 : ℝ) ≤ (radius 8 (16933/131072 : ℝ)) ∧ (radius 8 (16933/131072 : ℝ)) ≤ (245995280469/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16933/131072 : ℝ)) (314873959/320000000 : ℝ) (245995280469/250000000000 : ℝ) (22284086177/125000000000 : ℝ) (89136344711/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16933/131072 : ℝ)) (314873959/320000000 : ℝ) (245995280469/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (314873959/320000000 : ℝ) (245995280469/250000000000 : ℝ) (991990560937/1000000000000 : ℝ) (495995280469/500000000000 : ℝ) (991958225871/1000000000000 : ℝ) (991958225873/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 1 (991990560937/1000000000000 : ℝ) (495995280469/500000000000 : ℝ) (991958225871/1000000000000 : ℝ) (991958225873/1000000000000 : ℝ) (247993598351/250000000000 : ℝ) (495987196703/500000000000 : ℝ) (123996799159/125000000000 : ℝ) (495987196637/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 2 (247993598351/250000000000 : ℝ) (495987196703/500000000000 : ℝ) (123996799159/125000000000 : ℝ) (495987196637/500000000000 : ℝ) (495987196669/500000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 3 (495987196669/500000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 4 (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 5 (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 6 (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16933/131072 : ℝ)) 7 (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16933/131072 : ℝ))) (22284086177/125000000000 : ℝ) (89136344711/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22284086177/125000000000 : ℝ) (89136344711/500000000000 : ℝ) (147284086177/250000000000 : ℝ) (589136344711/1000000000000 : ℝ) (42222350647/100000000000 : ℝ) (211111753239/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 1 (147284086177/250000000000 : ℝ) (589136344711/1000000000000 : ℝ) (42222350647/100000000000 : ℝ) (211111753239/500000000000 : ℝ) (505679925589/1000000000000 : ℝ) (101135985119/200000000000 : ℝ) (62343204979/125000000000 : ℝ) (498745639839/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 2 (505679925589/1000000000000 : ℝ) (101135985119/200000000000 : ℝ) (62343204979/125000000000 : ℝ) (498745639839/1000000000000 : ℝ) (50221278271/100000000000 : ℝ) (502212782717/1000000000000 : ℝ) (502200814453/1000000000000 : ℝ) (502200814461/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 3 (50221278271/100000000000 : ℝ) (502212782717/1000000000000 : ℝ) (502200814453/1000000000000 : ℝ) (502200814461/1000000000000 : ℝ) (502206798581/1000000000000 : ℝ) (502206798589/1000000000000 : ℝ) (100441359709/200000000000 : ℝ) (251103399277/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 4 (502206798581/1000000000000 : ℝ) (502206798589/1000000000000 : ℝ) (100441359709/200000000000 : ℝ) (251103399277/500000000000 : ℝ) (502206798563/1000000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 5 (502206798563/1000000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 6 (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16933/131072 : ℝ))) 7 (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16933/131072 : ℝ)) hmem 8 (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16933/131072 : ℝ))) hcmem 8 (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16933/131072 : ℝ)) (991974393337/1000000000000 : ℝ) (49598719667/50000000000 : ℝ) (251103399281/500000000000 : ℝ) (125551699643/250000000000 : ℝ) (397623466779/500000000000 : ℝ) (397623466789/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1413_exp_lower
  have heNumeric : (2054902364741/1000000000000 : ℝ)/4 ≤ Real.exp (-5328528202999/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902364741/1000000000000 : ℝ)/4 ≤ Real.exp ((4233/32768 : ℝ)-(397623466789/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4233/32768 : ℝ) (16933/131072 : ℝ) (397623466789/500000000000 : ℝ) (2054902364741/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1414; no trusted numerical premise.
theorem cover8_leaf1414_exp_radius : (498991673037626683/500000000000000000 : ℝ) ≤ Real.exp ((-8467/524288 : ℝ)/8) ∧ Real.exp ((-8467/524288 : ℝ)/8) ≤ (997983346075253367/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8467/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1414_exp_lower : (460056750677808359/500000000000000000 : ℝ) ≤ Real.exp ((-21314110850539/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314110850539/32000000000000 : ℝ)/8) ≤ (920113501355616719/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314110850539/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1414_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451245349/500000000000 : ℝ) ≤ 4*Real.exp (16933/131072 : ℝ)*Real.exp (-mu (radius 8 (8467/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451245349/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8467/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1414_exp_radius
  have hrNumeric : (491990091739/500000000000 : ℝ) ≤ Real.exp (-8467/524288 : ℝ) ∧ Real.exp (-8467/524288 : ℝ) ≤ (983980183479/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491990091739/500000000000 : ℝ) ≤ (radius 8 (8467/65536 : ℝ)) ∧ (radius 8 (8467/65536 : ℝ)) ≤ (983980183479/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8467/65536 : ℝ)) (491990091739/500000000000 : ℝ) (983980183479/1000000000000 : ℝ) (178277868847/1000000000000 : ℝ) (178277868853/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8467/65536 : ℝ)) (491990091739/500000000000 : ℝ) (983980183479/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491990091739/500000000000 : ℝ) (983980183479/1000000000000 : ℝ) (991990091739/1000000000000 : ℝ) (49599504587/50000000000 : ℝ) (991957752869/1000000000000 : ℝ) (991957752871/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 1 (991990091739/1000000000000 : ℝ) (49599504587/50000000000 : ℝ) (991957752869/1000000000000 : ℝ) (991957752871/1000000000000 : ℝ) (1937449067/1953125000 : ℝ) (495986961153/500000000000 : ℝ) (247993480543/250000000000 : ℝ) (495986961087/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 2 (1937449067/1953125000 : ℝ) (495986961153/500000000000 : ℝ) (247993480543/250000000000 : ℝ) (495986961087/500000000000 : ℝ) (495986961119/500000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 3 (495986961119/500000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 4 (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 5 (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 6 (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8467/65536 : ℝ)) 7 (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8467/65536 : ℝ))) (178277868847/1000000000000 : ℝ) (178277868853/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178277868847/1000000000000 : ℝ) (178277868853/1000000000000 : ℝ) (589138934423/1000000000000 : ℝ) (589138934427/1000000000000 : ℝ) (422229639943/1000000000000 : ℝ) (422229639951/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 1 (589138934423/1000000000000 : ℝ) (589138934427/1000000000000 : ℝ) (422229639943/1000000000000 : ℝ) (422229639951/1000000000000 : ℝ) (505684287183/1000000000000 : ℝ) (505684287189/1000000000000 : ℝ) (249375179277/500000000000 : ℝ) (498750358561/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 2 (505684287183/1000000000000 : ℝ) (505684287189/1000000000000 : ℝ) (249375179277/500000000000 : ℝ) (498750358561/1000000000000 : ℝ) (125554330717/250000000000 : ℝ) (4017738583/8000000000 : ℝ) (31387834747/62500000000 : ℝ) (12555133899/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 3 (125554330717/250000000000 : ℝ) (4017738583/8000000000 : ℝ) (31387834747/62500000000 : ℝ) (12555133899/25000000000 : ℝ) (50221133941/100000000000 : ℝ) (251105669709/500000000000 : ℝ) (251105669687/500000000000 : ℝ) (251105669691/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 4 (50221133941/100000000000 : ℝ) (251105669709/500000000000 : ℝ) (251105669687/500000000000 : ℝ) (251105669691/500000000000 : ℝ) (3923526089/7812500000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 5 (3923526089/7812500000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 6 (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8467/65536 : ℝ))) 7 (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8467/65536 : ℝ)) hmem 8 (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8467/65536 : ℝ))) hcmem 8 (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8467/65536 : ℝ)) (991973922237/1000000000000 : ℝ) (3099918507/3125000000 : ℝ) (502211339391/1000000000000 : ℝ) (2511056697/5000000000 : ℝ) (795254501659/1000000000000 : ℝ) (795254501677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1414_exp_lower
  have heNumeric : (1027451245349/500000000000 : ℝ)/4 ≤ Real.exp (-21314110850539/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451245349/500000000000 : ℝ)/4 ≤ Real.exp ((16933/131072 : ℝ)-(795254501677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16933/131072 : ℝ) (8467/65536 : ℝ) (795254501677/1000000000000 : ℝ) (1027451245349/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1415; no trusted numerical premise.
theorem cover8_leaf1415_exp_radius : (249495806776593697/250000000000000000 : ℝ) ≤ Real.exp ((-16935/1048576 : ℝ)/8) ∧ Real.exp ((-16935/1048576 : ℝ)/8) ≤ (997983227106374789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16935/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1415_exp_lower : (28753547138749273/31250000000000000 : ℝ) ≤ Real.exp ((-10657054439741/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657054439741/16000000000000 : ℝ)/8) ≤ (920113508439976737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657054439741/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1415_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902617271/1000000000000 : ℝ) ≤ 4*Real.exp (8467/65536 : ℝ)*Real.exp (-mu (radius 8 (16935/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902617271/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16935/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1415_exp_radius
  have hrNumeric : (491989622541/500000000000 : ℝ) ≤ Real.exp (-16935/1048576 : ℝ) ∧ Real.exp (-16935/1048576 : ℝ) ≤ (983979245083/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491989622541/500000000000 : ℝ) ≤ (radius 8 (16935/131072 : ℝ)) ∧ (radius 8 (16935/131072 : ℝ)) ≤ (983979245083/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16935/131072 : ℝ)) (491989622541/500000000000 : ℝ) (983979245083/1000000000000 : ℝ) (178283048117/1000000000000 : ℝ) (178283048123/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16935/131072 : ℝ)) (491989622541/500000000000 : ℝ) (983979245083/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491989622541/500000000000 : ℝ) (983979245083/1000000000000 : ℝ) (991989622541/1000000000000 : ℝ) (495994811271/500000000000 : ℝ) (991957279867/1000000000000 : ℝ) (247989319967/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 1 (991989622541/1000000000000 : ℝ) (495994811271/500000000000 : ℝ) (991957279867/1000000000000 : ℝ) (247989319967/250000000000 : ℝ) (247993362801/250000000000 : ℝ) (198394690241/200000000000 : ℝ) (15499585173/15625000000 : ℝ) (495986725537/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 2 (247993362801/250000000000 : ℝ) (198394690241/200000000000 : ℝ) (15499585173/15625000000 : ℝ) (495986725537/500000000000 : ℝ) (495986725569/500000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 3 (495986725569/500000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 4 (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 5 (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 6 (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16935/131072 : ℝ)) 7 (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16935/131072 : ℝ))) (178283048117/1000000000000 : ℝ) (178283048123/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178283048117/1000000000000 : ℝ) (178283048123/1000000000000 : ℝ) (294570762029/500000000000 : ℝ) (294570762031/500000000000 : ℝ) (422235773137/1000000000000 : ℝ) (84447154629/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 1 (294570762029/500000000000 : ℝ) (294570762031/500000000000 : ℝ) (422235773137/1000000000000 : ℝ) (84447154629/200000000000 : ℝ) (505688648597/1000000000000 : ℝ) (126422162151/250000000000 : ℝ) (62344384633/125000000000 : ℝ) (31172192317/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 2 (505688648597/1000000000000 : ℝ) (126422162151/250000000000 : ℝ) (62344384633/125000000000 : ℝ) (31172192317/62500000000 : ℝ) (50222186283/100000000000 : ℝ) (251110931419/500000000000 : ℝ) (100441979451/200000000000 : ℝ) (31388118579/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 3 (50222186283/100000000000 : ℝ) (251110931419/500000000000 : ℝ) (100441979451/200000000000 : ℝ) (31388118579/62500000000 : ℝ) (251107940021/500000000000 : ℝ) (502215880051/1000000000000 : ℝ) (251107940003/500000000000 : ℝ) (31388492501/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 4 (251107940021/500000000000 : ℝ) (502215880051/1000000000000 : ℝ) (251107940003/500000000000 : ℝ) (31388492501/62500000000 : ℝ) (62776985003/125000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 5 (62776985003/125000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 6 (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16935/131072 : ℝ))) 7 (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16935/131072 : ℝ)) hmem 8 (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16935/131072 : ℝ))) hcmem 8 (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16935/131072 : ℝ)) (991973451137/1000000000000 : ℝ) (49598672557/50000000000 : ℝ) (502215880023/1000000000000 : ℝ) (251107940017/500000000000 : ℝ) (159052413891/200000000000 : ℝ) (198815517369/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1415_exp_lower
  have heNumeric : (2054902617271/1000000000000 : ℝ)/4 ≤ Real.exp (-10657054439741/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902617271/1000000000000 : ℝ)/4 ≤ Real.exp ((8467/65536 : ℝ)-(198815517369/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8467/65536 : ℝ) (16935/131072 : ℝ) (198815517369/250000000000 : ℝ) (2054902617271/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1416; no trusted numerical premise.
theorem cover8_leaf1416_exp_radius : (997983108137510393/1000000000000000000 : ℝ) ≤ Real.exp ((-2117/131072 : ℝ)/8) ∧ Real.exp ((-2117/131072 : ℝ)/8) ≤ (498991554068755197/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2117/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1416_exp_lower : (184022703111929233/200000000000000000 : ℝ) ≤ Real.exp ((-21314106898601/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314106898601/32000000000000 : ℝ)/8) ≤ (460056757779823083/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314106898601/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1416_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451372237/500000000000 : ℝ) ≤ 4*Real.exp (16935/131072 : ℝ)*Real.exp (-mu (radius 8 (2117/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451372237/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2117/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1416_exp_radius
  have hrNumeric : (983978306687/1000000000000 : ℝ) ≤ Real.exp (-2117/131072 : ℝ) ∧ Real.exp (-2117/131072 : ℝ) ≤ (7687330521/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983978306687/1000000000000 : ℝ) ≤ (radius 8 (2117/16384 : ℝ)) ∧ (radius 8 (2117/16384 : ℝ)) ≤ (7687330521/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2117/16384 : ℝ)) (983978306687/1000000000000 : ℝ) (7687330521/7812500000 : ℝ) (89144113613/500000000000 : ℝ) (5571507101/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2117/16384 : ℝ)) (983978306687/1000000000000 : ℝ) (7687330521/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983978306687/1000000000000 : ℝ) (7687330521/7812500000 : ℝ) (991989153343/1000000000000 : ℝ) (15499830521/15625000000 : ℝ) (198391361373/200000000000 : ℝ) (991956806867/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 1 (991989153343/1000000000000 : ℝ) (15499830521/15625000000 : ℝ) (198391361373/200000000000 : ℝ) (991956806867/1000000000000 : ℝ) (123996622513/125000000000 : ℝ) (495986490053/500000000000 : ℝ) (247993244993/250000000000 : ℝ) (495986489987/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 2 (123996622513/125000000000 : ℝ) (495986490053/500000000000 : ℝ) (247993244993/250000000000 : ℝ) (495986489987/500000000000 : ℝ) (495986490019/500000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 3 (495986490019/500000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 4 (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 5 (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 6 (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2117/16384 : ℝ)) 7 (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2117/16384 : ℝ))) (89144113613/500000000000 : ℝ) (5571507101/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89144113613/500000000000 : ℝ) (5571507101/31250000000 : ℝ) (589144113613/1000000000000 : ℝ) (36821507101/62500000000 : ℝ) (422241906051/1000000000000 : ℝ) (422241906059/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 1 (589144113613/1000000000000 : ℝ) (36821507101/62500000000 : ℝ) (422241906051/1000000000000 : ℝ) (422241906059/1000000000000 : ℝ) (63211626229/125000000000 : ℝ) (252846504919/500000000000 : ℝ) (498759795363/1000000000000 : ℝ) (49875979537/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 2 (63211626229/125000000000 : ℝ) (252846504919/500000000000 : ℝ) (498759795363/1000000000000 : ℝ) (49875979537/100000000000 : ℝ) (502226402597/1000000000000 : ℝ) (125556600651/250000000000 : ℝ) (502214438363/1000000000000 : ℝ) (50221443837/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 3 (502226402597/1000000000000 : ℝ) (125556600651/250000000000 : ℝ) (502214438363/1000000000000 : ℝ) (50221443837/100000000000 : ℝ) (784719407/1562500000 : ℝ) (502220420487/1000000000000 : ℝ) (125555105111/250000000000 : ℝ) (125555105113/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 4 (784719407/1562500000 : ℝ) (502220420487/1000000000000 : ℝ) (125555105111/250000000000 : ℝ) (125555105113/250000000000 : ℝ) (251110210231/500000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 5 (251110210231/500000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 6 (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2117/16384 : ℝ))) 7 (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2117/16384 : ℝ)) hmem 8 (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2117/16384 : ℝ))) hcmem 8 (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2117/16384 : ℝ)) (991972980037/1000000000000 : ℝ) (24799324501/25000000000 : ℝ) (502220420461/1000000000000 : ℝ) (50222042047/100000000000 : ℝ) (15905392739/20000000000 : ℝ) (99408704621/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1416_exp_lower
  have heNumeric : (1027451372237/500000000000 : ℝ)/4 ≤ Real.exp (-21314106898601/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451372237/500000000000 : ℝ)/4 ≤ Real.exp ((16935/131072 : ℝ)-(99408704621/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16935/131072 : ℝ) (2117/16384 : ℝ) (99408704621/125000000000 : ℝ) (1027451372237/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1417; no trusted numerical premise.
theorem cover8_leaf1417_exp_radius : (997982989168660179/1000000000000000000 : ℝ) ≤ Real.exp ((-16937/1048576 : ℝ)/8) ∧ Real.exp ((-16937/1048576 : ℝ)/8) ≤ (49899149458433009/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16937/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1417_exp_lower : (920113522713014807/1000000000000000000 : ℝ) ≤ Real.exp ((-2664263113543/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664263113543/4000000000000 : ℝ)/8) ≤ (115014190339126851/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664263113543/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1417_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372571807/25000000000 : ℝ) ≤ 4*Real.exp (2117/16384 : ℝ)*Real.exp (-mu (radius 8 (16937/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (51372571807/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16937/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1417_exp_radius
  have hrNumeric : (245994342073/250000000000 : ℝ) ≤ Real.exp (-16937/1048576 : ℝ) ∧ Real.exp (-16937/1048576 : ℝ) ≤ (983977368293/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245994342073/250000000000 : ℝ) ≤ (radius 8 (16937/131072 : ℝ)) ∧ (radius 8 (16937/131072 : ℝ)) ≤ (983977368293/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16937/131072 : ℝ)) (245994342073/250000000000 : ℝ) (983977368293/1000000000000 : ℝ) (178293406179/1000000000000 : ℝ) (89146703093/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16937/131072 : ℝ)) (245994342073/250000000000 : ℝ) (983977368293/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245994342073/250000000000 : ℝ) (983977368293/1000000000000 : ℝ) (495994342073/500000000000 : ℝ) (991988684147/1000000000000 : ℝ) (991956333863/1000000000000 : ℝ) (198391266773/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 1 (495994342073/500000000000 : ℝ) (991988684147/1000000000000 : ℝ) (991956333863/1000000000000 : ℝ) (198391266773/200000000000 : ℝ) (247993127251/250000000000 : ℝ) (495986254503/500000000000 : ℝ) (123996563609/125000000000 : ℝ) (7935780071/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 2 (247993127251/250000000000 : ℝ) (495986254503/500000000000 : ℝ) (123996563609/125000000000 : ℝ) (7935780071/8000000000 : ℝ) (495986254469/500000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 3 (495986254469/500000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 4 (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 5 (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 6 (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16937/131072 : ℝ)) 7 (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16937/131072 : ℝ))) (178293406179/1000000000000 : ℝ) (89146703093/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178293406179/1000000000000 : ℝ) (89146703093/500000000000 : ℝ) (589146703089/1000000000000 : ℝ) (589146703093/1000000000000 : ℝ) (422248038691/1000000000000 : ℝ) (422248038701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 1 (589146703089/1000000000000 : ℝ) (589146703093/1000000000000 : ℝ) (422248038691/1000000000000 : ℝ) (422248038701/1000000000000 : ℝ) (50569737089/100000000000 : ℝ) (505697370897/1000000000000 : ℝ) (498764513453/1000000000000 : ℝ) (249382256731/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 2 (50569737089/100000000000 : ℝ) (505697370897/1000000000000 : ℝ) (498764513453/1000000000000 : ℝ) (249382256731/500000000000 : ℝ) (502230942171/1000000000000 : ℝ) (25111547109/50000000000 : ℝ) (502218979277/1000000000000 : ℝ) (251109489643/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 3 (502230942171/1000000000000 : ℝ) (25111547109/50000000000 : ℝ) (502218979277/1000000000000 : ℝ) (251109489643/500000000000 : ℝ) (125556240181/250000000000 : ℝ) (502224960733/1000000000000 : ℝ) (31389060043/62500000000 : ℝ) (251112480349/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 4 (125556240181/250000000000 : ℝ) (502224960733/1000000000000 : ℝ) (31389060043/62500000000 : ℝ) (251112480349/500000000000 : ℝ) (251112480353/500000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 5 (251112480353/500000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 6 (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16937/131072 : ℝ))) 7 (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16937/131072 : ℝ)) hmem 8 (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16937/131072 : ℝ))) hcmem 8 (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16937/131072 : ℝ)) (991972508937/1000000000000 : ℝ) (991972508941/1000000000000 : ℝ) (100444992141/200000000000 : ℝ) (125556240179/250000000000 : ℝ) (159055440829/200000000000 : ℝ) (795277204167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1417_exp_lower
  have heNumeric : (51372571807/25000000000 : ℝ)/4 ≤ Real.exp (-2664263113543/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372571807/25000000000 : ℝ)/4 ≤ Real.exp ((2117/16384 : ℝ)-(795277204167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2117/16384 : ℝ) (16937/131072 : ℝ) (795277204167/1000000000000 : ℝ) (51372571807/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1418; no trusted numerical premise.
theorem cover8_leaf1418_exp_radius : (997982870199824147/1000000000000000000 : ℝ) ≤ Real.exp ((-8469/524288 : ℝ)/8) ∧ Real.exp ((-8469/524288 : ℝ)/8) ≤ (249495717549956037/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8469/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1418_exp_lower : (23002838247562449/25000000000000000 : ℝ) ≤ Real.exp ((-21314102908039/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314102908039/32000000000000 : ℝ)/8) ≤ (920113529902497961/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314102908039/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1418_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903000731/1000000000000 : ℝ) ≤ 4*Real.exp (16937/131072 : ℝ)*Real.exp (-mu (radius 8 (8469/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903000731/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8469/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1418_exp_radius
  have hrNumeric : (983976429899/1000000000000 : ℝ) ≤ Real.exp (-8469/524288 : ℝ) ∧ Real.exp (-8469/524288 : ℝ) ≤ (9839764299/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983976429899/1000000000000 : ℝ) ≤ (radius 8 (8469/65536 : ℝ)) ∧ (radius 8 (8469/65536 : ℝ)) ≤ (9839764299/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8469/65536 : ℝ)) (983976429899/1000000000000 : ℝ) (9839764299/10000000000 : ℝ) (178298584967/1000000000000 : ℝ) (178298584973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8469/65536 : ℝ)) (983976429899/1000000000000 : ℝ) (9839764299/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983976429899/1000000000000 : ℝ) (9839764299/10000000000 : ℝ) (991988214949/1000000000000 : ℝ) (19839764299/20000000000 : ℝ) (495977930431/500000000000 : ℝ) (991955860863/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 1 (991988214949/1000000000000 : ℝ) (19839764299/20000000000 : ℝ) (495977930431/500000000000 : ℝ) (991955860863/1000000000000 : ℝ) (198394407581/200000000000 : ℝ) (991972037907/1000000000000 : ℝ) (991972037773/1000000000000 : ℝ) (39678881511/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 2 (198394407581/200000000000 : ℝ) (991972037907/1000000000000 : ℝ) (991972037773/1000000000000 : ℝ) (39678881511/40000000000 : ℝ) (991972037839/1000000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 3 (991972037839/1000000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 4 (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 5 (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 6 (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8469/65536 : ℝ)) 7 (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8469/65536 : ℝ))) (178298584967/1000000000000 : ℝ) (178298584973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178298584967/1000000000000 : ℝ) (178298584973/1000000000000 : ℝ) (589149292483/1000000000000 : ℝ) (589149292487/1000000000000 : ℝ) (422254171047/1000000000000 : ℝ) (84450834211/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 1 (589149292483/1000000000000 : ℝ) (589149292487/1000000000000 : ℝ) (422254171047/1000000000000 : ℝ) (84450834211/200000000000 : ℝ) (101140346353/200000000000 : ℝ) (505701731771/1000000000000 : ℝ) (15586538479/31250000000 : ℝ) (62346153917/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 2 (101140346353/200000000000 : ℝ) (505701731771/1000000000000 : ℝ) (15586538479/31250000000 : ℝ) (62346153917/125000000000 : ℝ) (251117740773/500000000000 : ℝ) (251117740777/500000000000 : ℝ) (62777939999/125000000000 : ℝ) (3138897/6250000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 3 (251117740773/500000000000 : ℝ) (251117740777/500000000000 : ℝ) (62777939999/125000000000 : ℝ) (3138897/6250000 : ℝ) (502229500769/1000000000000 : ℝ) (502229500777/1000000000000 : ℝ) (502229500733/1000000000000 : ℝ) (251114750371/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 4 (502229500769/1000000000000 : ℝ) (502229500777/1000000000000 : ℝ) (502229500733/1000000000000 : ℝ) (251114750371/500000000000 : ℝ) (502229500751/1000000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 5 (502229500751/1000000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 6 (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8469/65536 : ℝ))) 7 (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8469/65536 : ℝ)) hmem 8 (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8469/65536 : ℝ))) hcmem 8 (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8469/65536 : ℝ)) (495986018919/500000000000 : ℝ) (991972037841/1000000000000 : ℝ) (2008918003/4000000000 : ℝ) (12555737519/25000000000 : ℝ) (795284771033/1000000000000 : ℝ) (198821192763/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1418_exp_lower
  have heNumeric : (2054903000731/1000000000000 : ℝ)/4 ≤ Real.exp (-21314102908039/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903000731/1000000000000 : ℝ)/4 ≤ Real.exp ((16937/131072 : ℝ)-(198821192763/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16937/131072 : ℝ) (8469/65536 : ℝ) (198821192763/250000000000 : ℝ) (2054903000731/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1419; no trusted numerical premise.
theorem cover8_leaf1419_exp_radius : (498991375615501149/500000000000000000 : ℝ) ≤ Real.exp ((-16939/1048576 : ℝ)/8) ∧ Real.exp ((-16939/1048576 : ℝ)/8) ≤ (997982751231002299/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16939/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1419_exp_lower : (460056768562897671/500000000000000000 : ℝ) ≤ Real.exp ((-10657050449163/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657050449163/16000000000000 : ℝ)/8) ≤ (920113537125795343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657050449163/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1419_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451564893/500000000000 : ℝ) ≤ 4*Real.exp (8469/65536 : ℝ)*Real.exp (-mu (radius 8 (16939/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451564893/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16939/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1419_exp_radius
  have hrNumeric : (491987745753/500000000000 : ℝ) ≤ Real.exp (-16939/1048576 : ℝ) ∧ Real.exp (-16939/1048576 : ℝ) ≤ (983975491507/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491987745753/500000000000 : ℝ) ≤ (radius 8 (16939/131072 : ℝ)) ∧ (radius 8 (16939/131072 : ℝ)) ≤ (983975491507/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16939/131072 : ℝ)) (491987745753/500000000000 : ℝ) (983975491507/1000000000000 : ℝ) (89151881799/500000000000 : ℝ) (35660752721/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16939/131072 : ℝ)) (491987745753/500000000000 : ℝ) (983975491507/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491987745753/500000000000 : ℝ) (983975491507/1000000000000 : ℝ) (991987745753/1000000000000 : ℝ) (495993872877/500000000000 : ℝ) (49597769393/50000000000 : ℝ) (495977693931/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 1 (991987745753/1000000000000 : ℝ) (495993872877/500000000000 : ℝ) (49597769393/50000000000 : ℝ) (495977693931/500000000000 : ℝ) (495985783403/500000000000 : ℝ) (123996445851/125000000000 : ℝ) (495985783337/500000000000 : ℝ) (991971566677/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 2 (495985783403/500000000000 : ℝ) (123996445851/125000000000 : ℝ) (495985783337/500000000000 : ℝ) (991971566677/1000000000000 : ℝ) (49598578337/50000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 3 (49598578337/50000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 4 (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 5 (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 6 (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16939/131072 : ℝ)) 7 (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16939/131072 : ℝ))) (89151881799/500000000000 : ℝ) (35660752721/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89151881799/500000000000 : ℝ) (35660752721/200000000000 : ℝ) (589151881799/1000000000000 : ℝ) (589151881803/1000000000000 : ℝ) (52782537891/125000000000 : ℝ) (422260303137/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 1 (589151881799/1000000000000 : ℝ) (589151881803/1000000000000 : ℝ) (52782537891/125000000000 : ℝ) (422260303137/1000000000000 : ℝ) (505706092463/1000000000000 : ℝ) (50570609247/100000000000 : ℝ) (99754789799/200000000000 : ℝ) (498773949003/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 2 (505706092463/1000000000000 : ℝ) (50570609247/100000000000 : ℝ) (99754789799/200000000000 : ℝ) (498773949003/1000000000000 : ℝ) (502240020729/1000000000000 : ℝ) (502240020737/1000000000000 : ℝ) (251114030257/500000000000 : ℝ) (502228060523/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 3 (502240020729/1000000000000 : ℝ) (502240020737/1000000000000 : ℝ) (251114030257/500000000000 : ℝ) (502228060523/1000000000000 : ℝ) (502234040621/1000000000000 : ℝ) (50223404063/100000000000 : ℝ) (100446808117/200000000000 : ℝ) (100446808119/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 4 (502234040621/1000000000000 : ℝ) (50223404063/100000000000 : ℝ) (100446808117/200000000000 : ℝ) (100446808119/200000000000 : ℝ) (502234040603/1000000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 5 (502234040603/1000000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 6 (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16939/131072 : ℝ))) 7 (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16939/131072 : ℝ)) hmem 8 (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16939/131072 : ℝ))) hcmem 8 (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16939/131072 : ℝ)) (991971566739/1000000000000 : ℝ) (991971566743/1000000000000 : ℝ) (251117020301/500000000000 : ℝ) (502234040613/1000000000000 : ℝ) (795292337621/1000000000000 : ℝ) (795292337643/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1419_exp_lower
  have heNumeric : (1027451564893/500000000000 : ℝ)/4 ≤ Real.exp (-10657050449163/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451564893/500000000000 : ℝ)/4 ≤ Real.exp ((8469/65536 : ℝ)-(795292337643/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8469/65536 : ℝ) (16939/131072 : ℝ) (795292337643/1000000000000 : ℝ) (1027451564893/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1420; no trusted numerical premise.
theorem cover8_leaf1420_exp_radius : (997982632262194631/1000000000000000000 : ℝ) ≤ Real.exp ((-4235/262144 : ℝ)/8) ∧ Real.exp ((-4235/262144 : ℝ)/8) ≤ (124747829032774329/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4235/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1420_exp_lower : (92011354438417211/100000000000000000 : ℝ) ≤ Real.exp ((-21314098878853/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314098878853/32000000000000 : ℝ)/8) ≤ (920113544384172111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314098878853/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1420_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725814867/250000000000 : ℝ) ≤ 4*Real.exp (16939/131072 : ℝ)*Real.exp (-mu (radius 8 (4235/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725814867/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4235/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1420_exp_radius
  have hrNumeric : (491987276557/500000000000 : ℝ) ≤ Real.exp (-4235/262144 : ℝ) ∧ Real.exp (-4235/262144 : ℝ) ≤ (196794910623/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491987276557/500000000000 : ℝ) ≤ (radius 8 (4235/32768 : ℝ)) ∧ (radius 8 (4235/32768 : ℝ)) ≤ (196794910623/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4235/32768 : ℝ)) (491987276557/500000000000 : ℝ) (196794910623/200000000000 : ℝ) (17830894207/100000000000 : ℝ) (44577235519/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4235/32768 : ℝ)) (491987276557/500000000000 : ℝ) (196794910623/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491987276557/500000000000 : ℝ) (196794910623/200000000000 : ℝ) (991987276557/1000000000000 : ℝ) (495993638279/500000000000 : ℝ) (991954914859/1000000000000 : ℝ) (991954914861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 1 (991987276557/1000000000000 : ℝ) (495993638279/500000000000 : ℝ) (991954914859/1000000000000 : ℝ) (991954914861/1000000000000 : ℝ) (247992773927/250000000000 : ℝ) (99197109571/100000000000 : ℝ) (123996386947/125000000000 : ℝ) (495985547789/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 2 (247992773927/250000000000 : ℝ) (99197109571/100000000000 : ℝ) (123996386947/125000000000 : ℝ) (495985547789/500000000000 : ℝ) (495985547821/500000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 3 (495985547821/500000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 4 (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 5 (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 6 (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4235/32768 : ℝ)) 7 (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4235/32768 : ℝ))) (17830894207/100000000000 : ℝ) (44577235519/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17830894207/100000000000 : ℝ) (44577235519/250000000000 : ℝ) (117830894207/200000000000 : ℝ) (294577235519/500000000000 : ℝ) (422266434931/1000000000000 : ℝ) (422266434939/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 1 (117830894207/200000000000 : ℝ) (294577235519/500000000000 : ℝ) (422266434931/1000000000000 : ℝ) (422266434939/1000000000000 : ℝ) (505710452983/1000000000000 : ℝ) (505710452989/1000000000000 : ℝ) (498778666451/1000000000000 : ℝ) (249389333229/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 2 (505710452983/1000000000000 : ℝ) (505710452989/1000000000000 : ℝ) (498778666451/1000000000000 : ℝ) (249389333229/500000000000 : ℝ) (502244559717/1000000000000 : ℝ) (125561139931/250000000000 : ℝ) (251116300421/500000000000 : ℝ) (10044652017/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 3 (502244559717/1000000000000 : ℝ) (125561139931/250000000000 : ℝ) (251116300421/500000000000 : ℝ) (10044652017/20000000000 : ℝ) (502238580279/1000000000000 : ℝ) (502238580287/1000000000000 : ℝ) (502238580243/1000000000000 : ℝ) (125559645063/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 4 (502238580279/1000000000000 : ℝ) (502238580287/1000000000000 : ℝ) (502238580243/1000000000000 : ℝ) (125559645063/250000000000 : ℝ) (502238580261/1000000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 5 (502238580261/1000000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 6 (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4235/32768 : ℝ))) 7 (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4235/32768 : ℝ)) hmem 8 (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4235/32768 : ℝ))) hcmem 8 (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4235/32768 : ℝ)) (991971095641/1000000000000 : ℝ) (247992773911/250000000000 : ℝ) (25111929013/50000000000 : ℝ) (50223858027/100000000000 : ℝ) (795299903909/1000000000000 : ℝ) (795299903929/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1420_exp_lower
  have heNumeric : (513725814867/250000000000 : ℝ)/4 ≤ Real.exp (-21314098878853/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725814867/250000000000 : ℝ)/4 ≤ Real.exp ((16939/131072 : ℝ)-(795299903929/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16939/131072 : ℝ) (4235/32768 : ℝ) (795299903929/1000000000000 : ℝ) (513725814867/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1421; no trusted numerical premise.
theorem cover8_leaf1421_exp_radius : (498991256646700573/500000000000000000 : ℝ) ≤ Real.exp ((-16941/1048576 : ℝ)/8) ∧ Real.exp ((-16941/1048576 : ℝ)/8) ≤ (997982513293401147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16941/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1421_exp_lower : (460056775839101667/500000000000000000 : ℝ) ≤ Real.exp ((-1065704842473/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065704842473/1600000000000 : ℝ)/8) ≤ (184022710335640667/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065704842473/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1421_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903389787/1000000000000 : ℝ) ≤ 4*Real.exp (4235/32768 : ℝ)*Real.exp (-mu (radius 8 (16941/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903389787/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16941/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1421_exp_radius
  have hrNumeric : (245993403681/250000000000 : ℝ) ≤ Real.exp (-16941/1048576 : ℝ) ∧ Real.exp (-16941/1048576 : ℝ) ≤ (39358944589/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245993403681/250000000000 : ℝ) ≤ (radius 8 (16941/131072 : ℝ)) ∧ (radius 8 (16941/131072 : ℝ)) ≤ (39358944589/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16941/131072 : ℝ)) (245993403681/250000000000 : ℝ) (39358944589/40000000000 : ℝ) (89157060187/500000000000 : ℝ) (178314120381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16941/131072 : ℝ)) (245993403681/250000000000 : ℝ) (39358944589/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245993403681/250000000000 : ℝ) (39358944589/40000000000 : ℝ) (495993403681/500000000000 : ℝ) (991986807363/1000000000000 : ℝ) (991954441859/1000000000000 : ℝ) (49597722093/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 1 (495993403681/500000000000 : ℝ) (991986807363/1000000000000 : ℝ) (991954441859/1000000000000 : ℝ) (49597722093/50000000000 : ℝ) (99197062461/100000000000 : ℝ) (247992656153/250000000000 : ℝ) (495985312239/500000000000 : ℝ) (6199816403/6250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 2 (99197062461/100000000000 : ℝ) (247992656153/250000000000 : ℝ) (495985312239/500000000000 : ℝ) (6199816403/6250000000 : ℝ) (30999082017/31250000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 3 (30999082017/31250000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 4 (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 5 (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 6 (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16941/131072 : ℝ)) 7 (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16941/131072 : ℝ))) (89157060187/500000000000 : ℝ) (178314120381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89157060187/500000000000 : ℝ) (178314120381/1000000000000 : ℝ) (589157060187/1000000000000 : ℝ) (589157060191/1000000000000 : ℝ) (422272566447/1000000000000 : ℝ) (52784070807/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 1 (589157060187/1000000000000 : ℝ) (589157060191/1000000000000 : ℝ) (422272566447/1000000000000 : ℝ) (52784070807/125000000000 : ℝ) (505714813317/1000000000000 : ℝ) (126428703331/250000000000 : ℝ) (49878338369/100000000000 : ℝ) (249391691849/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 2 (505714813317/1000000000000 : ℝ) (126428703331/250000000000 : ℝ) (49878338369/100000000000 : ℝ) (249391691849/500000000000 : ℝ) (502249098503/1000000000000 : ℝ) (502249098511/1000000000000 : ℝ) (62779642621/125000000000 : ℝ) (502237140977/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 3 (502249098503/1000000000000 : ℝ) (502249098511/1000000000000 : ℝ) (62779642621/125000000000 : ℝ) (502237140977/1000000000000 : ℝ) (100448623947/200000000000 : ℝ) (3923774373/7812500000 : ℝ) (502243119699/1000000000000 : ℝ) (502243119709/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 4 (100448623947/200000000000 : ℝ) (3923774373/7812500000 : ℝ) (502243119699/1000000000000 : ℝ) (502243119709/1000000000000 : ℝ) (502243119717/1000000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 5 (502243119717/1000000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 6 (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16941/131072 : ℝ))) 7 (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16941/131072 : ℝ)) hmem 8 (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16941/131072 : ℝ))) hcmem 8 (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16941/131072 : ℝ)) (991970624543/1000000000000 : ℝ) (495985312273/500000000000 : ℝ) (125560779929/250000000000 : ℝ) (502243119727/1000000000000 : ℝ) (198826867471/250000000000 : ℝ) (159061493981/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1421_exp_lower
  have heNumeric : (2054903389787/1000000000000 : ℝ)/4 ≤ Real.exp (-1065704842473/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903389787/1000000000000 : ℝ)/4 ≤ Real.exp ((4235/32768 : ℝ)-(159061493981/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4235/32768 : ℝ) (16941/131072 : ℝ) (159061493981/200000000000 : ℝ) (2054903389787/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1422; no trusted numerical premise.
theorem cover8_leaf1422_exp_radius : (997982394324621843/1000000000000000000 : ℝ) ≤ Real.exp ((-8471/524288 : ℝ)/8) ∧ Real.exp ((-8471/524288 : ℝ)/8) ≤ (249495598581155461/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8471/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1422_exp_lower : (920113559006393833/1000000000000000000 : ℝ) ≤ Real.exp ((-21314094810563/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314094810563/32000000000000 : ℝ)/8) ≤ (460056779503196917/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314094810563/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1422_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725880179/250000000000 : ℝ) ≤ 4*Real.exp (16941/131072 : ℝ)*Real.exp (-mu (radius 8 (8471/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725880179/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8471/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1422_exp_radius
  have hrNumeric : (491986338167/500000000000 : ℝ) ≤ Real.exp (-8471/524288 : ℝ) ∧ Real.exp (-8471/524288 : ℝ) ≤ (196794535267/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491986338167/500000000000 : ℝ) ≤ (radius 8 (8471/65536 : ℝ)) ∧ (radius 8 (8471/65536 : ℝ)) ≤ (196794535267/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8471/65536 : ℝ)) (491986338167/500000000000 : ℝ) (196794535267/200000000000 : ℝ) (44579824631/250000000000 : ℝ) (17831929853/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8471/65536 : ℝ)) (491986338167/500000000000 : ℝ) (196794535267/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491986338167/500000000000 : ℝ) (196794535267/200000000000 : ℝ) (991986338167/1000000000000 : ℝ) (123998292271/125000000000 : ℝ) (495976984429/500000000000 : ℝ) (991953968859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 1 (991986338167/1000000000000 : ℝ) (123998292271/125000000000 : ℝ) (495976984429/500000000000 : ℝ) (991953968859/1000000000000 : ℝ) (123996269189/125000000000 : ℝ) (495985076757/500000000000 : ℝ) (49598507669/50000000000 : ℝ) (495985076691/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 2 (123996269189/125000000000 : ℝ) (495985076757/500000000000 : ℝ) (49598507669/50000000000 : ℝ) (495985076691/500000000000 : ℝ) (495985076723/500000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 3 (495985076723/500000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 4 (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 5 (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 6 (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8471/65536 : ℝ)) 7 (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8471/65536 : ℝ))) (44579824631/250000000000 : ℝ) (17831929853/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44579824631/250000000000 : ℝ) (17831929853/100000000000 : ℝ) (294579824631/500000000000 : ℝ) (117831929853/200000000000 : ℝ) (422278697691/1000000000000 : ℝ) (422278697699/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 1 (294579824631/500000000000 : ℝ) (117831929853/200000000000 : ℝ) (422278697691/1000000000000 : ℝ) (422278697699/1000000000000 : ℝ) (126429793369/250000000000 : ℝ) (252859586741/500000000000 : ℝ) (249394050361/500000000000 : ℝ) (498788100729/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 2 (126429793369/250000000000 : ℝ) (252859586741/500000000000 : ℝ) (249394050361/500000000000 : ℝ) (498788100729/1000000000000 : ℝ) (502253637099/1000000000000 : ℝ) (251126818553/500000000000 : ℝ) (502241680903/1000000000000 : ℝ) (502241680911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 3 (502253637099/1000000000000 : ℝ) (251126818553/500000000000 : ℝ) (502241680903/1000000000000 : ℝ) (502241680911/1000000000000 : ℝ) (502247659001/1000000000000 : ℝ) (502247659009/1000000000000 : ℝ) (100449531793/200000000000 : ℝ) (502247658973/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 4 (502247659001/1000000000000 : ℝ) (502247659009/1000000000000 : ℝ) (100449531793/200000000000 : ℝ) (502247658973/1000000000000 : ℝ) (502247658983/1000000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 5 (502247658983/1000000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 6 (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8471/65536 : ℝ))) 7 (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8471/65536 : ℝ)) hmem 8 (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8471/65536 : ℝ))) hcmem 8 (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8471/65536 : ℝ)) (198394030689/200000000000 : ℝ) (123996269181/125000000000 : ℝ) (251123829491/500000000000 : ℝ) (502247658991/1000000000000 : ℝ) (397657517783/500000000000 : ℝ) (12426797431/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1422_exp_lower
  have heNumeric : (513725880179/250000000000 : ℝ)/4 ≤ Real.exp (-21314094810563/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725880179/250000000000 : ℝ)/4 ≤ Real.exp ((16941/131072 : ℝ)-(12426797431/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16941/131072 : ℝ) (8471/65536 : ℝ) (12426797431/15625000000 : ℝ) (513725880179/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1423; no trusted numerical premise.
theorem cover8_leaf1423_exp_radius : (997982275355856723/1000000000000000000 : ℝ) ≤ Real.exp ((-16943/1048576 : ℝ)/8) ∧ Real.exp ((-16943/1048576 : ℝ)/8) ≤ (249495568838964181/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16943/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1423_exp_lower : (920113566369318677/1000000000000000000 : ℝ) ≤ Real.exp ((-10657046381001/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657046381001/16000000000000 : ℝ)/8) ≤ (460056783184659339/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657046381001/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1423_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451826133/500000000000 : ℝ) ≤ 4*Real.exp (8471/65536 : ℝ)*Real.exp (-mu (radius 8 (16943/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451826133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16943/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1423_exp_radius
  have hrNumeric : (196794347589/200000000000 : ℝ) ≤ Real.exp (-16943/1048576 : ℝ) ∧ Real.exp (-16943/1048576 : ℝ) ≤ (491985868973/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196794347589/200000000000 : ℝ) ≤ (radius 8 (16943/131072 : ℝ)) ∧ (radius 8 (16943/131072 : ℝ)) ≤ (491985868973/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16943/131072 : ℝ)) (196794347589/200000000000 : ℝ) (491985868973/500000000000 : ℝ) (5572639891/31250000000 : ℝ) (178324476519/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16943/131072 : ℝ)) (196794347589/200000000000 : ℝ) (491985868973/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196794347589/200000000000 : ℝ) (491985868973/500000000000 : ℝ) (247996467243/250000000000 : ℝ) (991985868973/1000000000000 : ℝ) (495976747929/500000000000 : ℝ) (991953495859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 1 (247996467243/250000000000 : ℝ) (991985868973/1000000000000 : ℝ) (495976747929/500000000000 : ℝ) (991953495859/1000000000000 : ℝ) (198393936483/200000000000 : ℝ) (61998105151/62500000000 : ℝ) (495984841141/500000000000 : ℝ) (247992420571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 2 (198393936483/200000000000 : ℝ) (61998105151/62500000000 : ℝ) (495984841141/500000000000 : ℝ) (247992420571/250000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 3 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 4 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 5 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 6 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16943/131072 : ℝ)) 7 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16943/131072 : ℝ))) (5572639891/31250000000 : ℝ) (178324476519/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5572639891/31250000000 : ℝ) (178324476519/1000000000000 : ℝ) (36822639891/62500000000 : ℝ) (29458111913/50000000000 : ℝ) (211142414327/500000000000 : ℝ) (52785603583/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 1 (36822639891/62500000000 : ℝ) (29458111913/50000000000 : ℝ) (211142414327/500000000000 : ℝ) (52785603583/125000000000 : ℝ) (101144706691/200000000000 : ℝ) (252861766731/500000000000 : ℝ) (498792817541/1000000000000 : ℝ) (9975856351/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 2 (101144706691/200000000000 : ℝ) (252861766731/500000000000 : ℝ) (498792817541/1000000000000 : ℝ) (9975856351/20000000000 : ℝ) (251129087749/500000000000 : ℝ) (251129087753/500000000000 : ℝ) (502246220641/1000000000000 : ℝ) (10044924413/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 3 (251129087749/500000000000 : ℝ) (251129087753/500000000000 : ℝ) (502246220641/1000000000000 : ℝ) (10044924413/20000000000 : ℝ) (502252198069/1000000000000 : ℝ) (251126099039/500000000000 : ℝ) (502252198033/1000000000000 : ℝ) (502252198043/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 4 (502252198069/1000000000000 : ℝ) (251126099039/500000000000 : ℝ) (502252198033/1000000000000 : ℝ) (502252198043/1000000000000 : ℝ) (502252198051/1000000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 5 (502252198051/1000000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 6 (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16943/131072 : ℝ))) 7 (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16943/131072 : ℝ)) hmem 8 (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16943/131072 : ℝ))) hcmem 8 (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16943/131072 : ℝ)) (247992420587/250000000000 : ℝ) (19839393647/20000000000 : ℝ) (10045043961/20000000000 : ℝ) (502252198061/1000000000000 : ℝ) (795322600941/1000000000000 : ℝ) (795322600961/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1423_exp_lower
  have heNumeric : (1027451826133/500000000000 : ℝ)/4 ≤ Real.exp (-10657046381001/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451826133/500000000000 : ℝ)/4 ≤ Real.exp ((8471/65536 : ℝ)-(795322600961/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8471/65536 : ℝ) (16943/131072 : ℝ) (795322600961/1000000000000 : ℝ) (1027451826133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1424; no trusted numerical premise.
theorem cover8_leaf1424_exp_radius : (199596431277421157/200000000000000000 : ℝ) ≤ Real.exp ((-1059/65536 : ℝ)/8) ∧ Real.exp ((-1059/65536 : ℝ)/8) ≤ (498991078193552893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1059/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1424_exp_lower : (920113573766402797/1000000000000000000 : ℝ) ≤ Real.exp ((-21314090703937/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314090703937/32000000000000 : ℝ)/8) ≤ (460056786883201399/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314090703937/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1424_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451892213/500000000000 : ℝ) ≤ 4*Real.exp (16943/131072 : ℝ)*Real.exp (-mu (radius 8 (1059/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451892213/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1059/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1424_exp_radius
  have hrNumeric : (245992699889/250000000000 : ℝ) ≤ Real.exp (-1059/65536 : ℝ) ∧ Real.exp (-1059/65536 : ℝ) ≤ (983970799557/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245992699889/250000000000 : ℝ) ≤ (radius 8 (1059/8192 : ℝ)) ∧ (radius 8 (1059/8192 : ℝ)) ≤ (983970799557/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1059/8192 : ℝ)) (245992699889/250000000000 : ℝ) (983970799557/1000000000000 : ℝ) (35665930869/200000000000 : ℝ) (11145603397/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1059/8192 : ℝ)) (245992699889/250000000000 : ℝ) (983970799557/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245992699889/250000000000 : ℝ) (983970799557/1000000000000 : ℝ) (495992699889/500000000000 : ℝ) (991985399779/1000000000000 : ℝ) (991953022857/1000000000000 : ℝ) (495976511429/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 1 (495992699889/500000000000 : ℝ) (991985399779/1000000000000 : ℝ) (991953022857/1000000000000 : ℝ) (495976511429/500000000000 : ℝ) (991969211317/1000000000000 : ℝ) (991969211319/1000000000000 : ℝ) (198393842237/200000000000 : ℝ) (991969211187/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 2 (991969211317/1000000000000 : ℝ) (991969211319/1000000000000 : ℝ) (198393842237/200000000000 : ℝ) (991969211187/1000000000000 : ℝ) (991969211251/1000000000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 3 (991969211251/1000000000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 4 (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 5 (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 6 (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1059/8192 : ℝ)) 7 (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1059/8192 : ℝ))) (35665930869/200000000000 : ℝ) (11145603397/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35665930869/200000000000 : ℝ) (11145603397/62500000000 : ℝ) (147291206793/250000000000 : ℝ) (73645603397/125000000000 : ℝ) (84458191869/200000000000 : ℝ) (211145479677/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 1 (147291206793/250000000000 : ℝ) (73645603397/125000000000 : ℝ) (84458191869/200000000000 : ℝ) (211145479677/500000000000 : ℝ) (252863946629/500000000000 : ℝ) (101145578653/200000000000 : ℝ) (249398767077/500000000000 : ℝ) (249398767081/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 2 (252863946629/500000000000 : ℝ) (101145578653/200000000000 : ℝ) (249398767077/500000000000 : ℝ) (249398767081/500000000000 : ℝ) (251131356853/500000000000 : ℝ) (251131356857/500000000000 : ℝ) (125562690047/250000000000 : ℝ) (502250760197/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 3 (251131356853/500000000000 : ℝ) (251131356857/500000000000 : ℝ) (125562690047/250000000000 : ℝ) (502250760197/1000000000000 : ℝ) (502256736947/1000000000000 : ℝ) (125564184239/250000000000 : ℝ) (502256736911/1000000000000 : ℝ) (12556418423/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 4 (502256736947/1000000000000 : ℝ) (125564184239/250000000000 : ℝ) (502256736911/1000000000000 : ℝ) (12556418423/25000000000 : ℝ) (502256736929/1000000000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 5 (502256736929/1000000000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 6 (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1059/8192 : ℝ))) 7 (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1059/8192 : ℝ)) hmem 8 (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1059/8192 : ℝ))) hcmem 8 (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1059/8192 : ℝ)) (793575369/800000000 : ℝ) (991969211253/1000000000000 : ℝ) (15695523029/31250000000 : ℝ) (251128368469/500000000000 : ℝ) (795330166021/1000000000000 : ℝ) (795330166041/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1424_exp_lower
  have heNumeric : (1027451892213/500000000000 : ℝ)/4 ≤ Real.exp (-21314090703937/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451892213/500000000000 : ℝ)/4 ≤ Real.exp ((16943/131072 : ℝ)-(795330166041/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16943/131072 : ℝ) (1059/8192 : ℝ) (795330166041/1000000000000 : ℝ) (1027451892213/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1400_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1400_certificate
#check SmaleRate.Proofs.cover8_leaf1401_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1401_certificate
#check SmaleRate.Proofs.cover8_leaf1402_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1402_certificate
#check SmaleRate.Proofs.cover8_leaf1403_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1403_certificate
#check SmaleRate.Proofs.cover8_leaf1404_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1404_certificate
#check SmaleRate.Proofs.cover8_leaf1405_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1405_certificate
#check SmaleRate.Proofs.cover8_leaf1406_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1406_certificate
#check SmaleRate.Proofs.cover8_leaf1407_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1407_certificate
#check SmaleRate.Proofs.cover8_leaf1408_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1408_certificate
#check SmaleRate.Proofs.cover8_leaf1409_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1409_certificate
#check SmaleRate.Proofs.cover8_leaf1410_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1410_certificate
#check SmaleRate.Proofs.cover8_leaf1411_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1411_certificate
#check SmaleRate.Proofs.cover8_leaf1412_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1412_certificate
#check SmaleRate.Proofs.cover8_leaf1413_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1413_certificate
#check SmaleRate.Proofs.cover8_leaf1414_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1414_certificate
#check SmaleRate.Proofs.cover8_leaf1415_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1415_certificate
#check SmaleRate.Proofs.cover8_leaf1416_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1416_certificate
#check SmaleRate.Proofs.cover8_leaf1417_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1417_certificate
#check SmaleRate.Proofs.cover8_leaf1418_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1418_certificate
#check SmaleRate.Proofs.cover8_leaf1419_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1419_certificate
#check SmaleRate.Proofs.cover8_leaf1420_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1420_certificate
#check SmaleRate.Proofs.cover8_leaf1421_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1421_certificate
#check SmaleRate.Proofs.cover8_leaf1422_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1422_certificate
#check SmaleRate.Proofs.cover8_leaf1423_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1423_certificate
#check SmaleRate.Proofs.cover8_leaf1424_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1424_certificate
