/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0275; no trusted numerical premise.
theorem cover8_leaf0275_exp_radius : (499017370978627129/500000000000000000 : ℝ) ≤ Real.exp ((-8251/524288 : ℝ)/8) ∧ Real.exp ((-8251/524288 : ℝ)/8) ≤ (998034741957254259/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8251/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0275_exp_lower : (230028437083430887/250000000000000000 : ℝ) ≤ Real.exp ((-21314042134683/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314042134683/32000000000000 : ℝ)/8) ≤ (920113748333723549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314042134683/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0275_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906903339/1000000000000 : ℝ) ≤ 4*Real.exp (16501/131072 : ℝ)*Real.exp (-mu (radius 8 (8251/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906903339/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8251/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0275_exp_radius
  have hrNumeric : (49219282717/50000000000 : ℝ) ≤ Real.exp (-8251/524288 : ℝ) ∧ Real.exp (-8251/524288 : ℝ) ≤ (984385654341/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49219282717/50000000000 : ℝ) ≤ (radius 8 (8251/65536 : ℝ)) ∧ (radius 8 (8251/65536 : ℝ)) ≤ (984385654341/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8251/65536 : ℝ)) (49219282717/50000000000 : ℝ) (984385654341/1000000000000 : ℝ) (35205047097/200000000000 : ℝ) (176025235491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8251/65536 : ℝ)) (49219282717/50000000000 : ℝ) (984385654341/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49219282717/50000000000 : ℝ) (984385654341/1000000000000 : ℝ) (99219282717/100000000000 : ℝ) (992192827171/1000000000000 : ℝ) (992162110917/1000000000000 : ℝ) (496081055459/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 1 (99219282717/100000000000 : ℝ) (992192827171/1000000000000 : ℝ) (992162110917/1000000000000 : ℝ) (496081055459/500000000000 : ℝ) (992177469043/1000000000000 : ℝ) (198435493809/200000000000 : ℝ) (248044367231/250000000000 : ℝ) (496088734463/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 2 (992177469043/1000000000000 : ℝ) (198435493809/200000000000 : ℝ) (248044367231/250000000000 : ℝ) (496088734463/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 3 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 4 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 5 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 6 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8251/65536 : ℝ)) 7 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8251/65536 : ℝ))) (35205047097/200000000000 : ℝ) (176025235491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35205047097/200000000000 : ℝ) (176025235491/1000000000000 : ℝ) (294006308871/500000000000 : ℝ) (294006308873/500000000000 : ℝ) (419553614553/1000000000000 : ℝ) (419553614561/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 1 (294006308871/500000000000 : ℝ) (294006308873/500000000000 : ℝ) (419553614553/1000000000000 : ℝ) (419553614561/1000000000000 : ℝ) (503783116147/1000000000000 : ℝ) (251891558077/500000000000 : ℝ) (15521621109/31250000000 : ℝ) (62086484437/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 2 (503783116147/1000000000000 : ℝ) (251891558077/500000000000 : ℝ) (15521621109/31250000000 : ℝ) (62086484437/125000000000 : ℝ) (500237495817/1000000000000 : ℝ) (20009499833/40000000000 : ℝ) (125056232551/250000000000 : ℝ) (500224930213/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 3 (500237495817/1000000000000 : ℝ) (20009499833/40000000000 : ℝ) (125056232551/250000000000 : ℝ) (500224930213/1000000000000 : ℝ) (50023121301/100000000000 : ℝ) (500231213019/1000000000000 : ℝ) (500231212971/1000000000000 : ℝ) (25011560649/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 4 (50023121301/100000000000 : ℝ) (500231213019/1000000000000 : ℝ) (500231212971/1000000000000 : ℝ) (25011560649/50000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 5 (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 6 (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8251/65536 : ℝ))) 7 (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8251/65536 : ℝ)) hmem 8 (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8251/65536 : ℝ))) hcmem 8 (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8251/65536 : ℝ)) (992177468983/1000000000000 : ℝ) (496088734493/500000000000 : ℝ) (50023121299/100000000000 : ℝ) (500231213/1000000000 : ℝ) (15839129117/20000000000 : ℝ) (791956455869/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0275_exp_lower
  have heNumeric : (2054906903339/1000000000000 : ℝ)/4 ≤ Real.exp (-21314042134683/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906903339/1000000000000 : ℝ)/4 ≤ Real.exp ((16501/131072 : ℝ)-(791956455869/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16501/131072 : ℝ) (8251/65536 : ℝ) (791956455869/1000000000000 : ℝ) (2054906903339/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0276; no trusted numerical premise.
theorem cover8_leaf0276_exp_radius : (499017311491124407/500000000000000000 : ℝ) ≤ Real.exp ((-16503/1048576 : ℝ)/8) ∧ Real.exp ((-16503/1048576 : ℝ)/8) ≤ (199606924596449763/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16503/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0276_exp_lower : (36804549601001701/40000000000000000 : ℝ) ≤ Real.exp ((-10657022223189/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657022223189/16000000000000 : ℝ)/8) ≤ (460056870012521263/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657022223189/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0276_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726688723/250000000000 : ℝ) ≤ 4*Real.exp (8251/65536 : ℝ)*Real.exp (-mu (radius 8 (16503/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726688723/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16503/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0276_exp_radius
  have hrNumeric : (984384715557/1000000000000 : ℝ) ≤ Real.exp (-16503/1048576 : ℝ) ∧ Real.exp (-16503/1048576 : ℝ) ≤ (492192357779/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984384715557/1000000000000 : ℝ) ≤ (radius 8 (16503/131072 : ℝ)) ∧ (radius 8 (16503/131072 : ℝ)) ≤ (492192357779/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16503/131072 : ℝ)) (984384715557/1000000000000 : ℝ) (492192357779/500000000000 : ℝ) (176030485359/1000000000000 : ℝ) (35206097073/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16503/131072 : ℝ)) (984384715557/1000000000000 : ℝ) (492192357779/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984384715557/1000000000000 : ℝ) (492192357779/500000000000 : ℝ) (496096178889/500000000000 : ℝ) (992192357779/1000000000000 : ℝ) (992161637817/1000000000000 : ℝ) (992161637819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 1 (496096178889/500000000000 : ℝ) (992192357779/1000000000000 : ℝ) (992161637817/1000000000000 : ℝ) (992161637819/1000000000000 : ℝ) (992176997797/1000000000000 : ℝ) (992176997799/1000000000000 : ℝ) (496088498839/500000000000 : ℝ) (992176997681/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 2 (992176997797/1000000000000 : ℝ) (992176997799/1000000000000 : ℝ) (496088498839/500000000000 : ℝ) (992176997681/1000000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 3 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 4 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 5 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 6 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16503/131072 : ℝ)) 7 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16503/131072 : ℝ))) (176030485359/1000000000000 : ℝ) (35206097073/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176030485359/1000000000000 : ℝ) (35206097073/200000000000 : ℝ) (588015242679/1000000000000 : ℝ) (588015242683/1000000000000 : ℝ) (209779935503/500000000000 : ℝ) (209779935507/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 1 (588015242679/1000000000000 : ℝ) (588015242683/1000000000000 : ℝ) (209779935503/500000000000 : ℝ) (209779935507/500000000000 : ℝ) (251893778421/500000000000 : ℝ) (503787556849/1000000000000 : ℝ) (248348343747/500000000000 : ℝ) (496696687501/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 2 (251893778421/500000000000 : ℝ) (503787556849/1000000000000 : ℝ) (248348343747/500000000000 : ℝ) (496696687501/1000000000000 : ℝ) (62530265271/125000000000 : ℝ) (20009684887/40000000000 : ℝ) (500229557987/1000000000000 : ℝ) (100045911599/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 3 (62530265271/125000000000 : ℝ) (20009684887/40000000000 : ℝ) (500229557987/1000000000000 : ℝ) (100045911599/200000000000 : ℝ) (500235840077/1000000000000 : ℝ) (100047168017/200000000000 : ℝ) (250117920019/500000000000 : ℝ) (250117920023/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 4 (500235840077/1000000000000 : ℝ) (100047168017/200000000000 : ℝ) (250117920019/500000000000 : ℝ) (250117920023/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 5 (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 6 (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16503/131072 : ℝ))) 7 (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16503/131072 : ℝ)) hmem 8 (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16503/131072 : ℝ))) hcmem 8 (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16503/131072 : ℝ)) (992176997737/1000000000000 : ℝ) (49608849887/50000000000 : ℝ) (500235840057/1000000000000 : ℝ) (250117920033/500000000000 : ℝ) (395982078743/500000000000 : ℝ) (12374439961/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0276_exp_lower
  have heNumeric : (513726688723/250000000000 : ℝ)/4 ≤ Real.exp (-10657022223189/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726688723/250000000000 : ℝ)/4 ≤ Real.exp ((8251/65536 : ℝ)-(12374439961/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8251/65536 : ℝ) (16503/131072 : ℝ) (12374439961/15625000000 : ℝ) (513726688723/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0277; no trusted numerical premise.
theorem cover8_leaf0277_exp_radius : (998034504007257553/1000000000000000000 : ℝ) ≤ Real.exp ((-2063/131072 : ℝ)/8) ∧ Real.exp ((-2063/131072 : ℝ)/8) ≤ (499017252003628777/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2063/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0277_exp_lower : (230028432938464053/250000000000000000 : ℝ) ≤ Real.exp ((-21314046747641/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314046747641/32000000000000 : ℝ)/8) ≤ (920113731753856213/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314046747641/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0277_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981321423/200000000000 : ℝ) ≤ 4*Real.exp (16503/131072 : ℝ)*Real.exp (-mu (radius 8 (2063/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410981321423/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2063/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0277_exp_radius
  have hrNumeric : (123047972097/125000000000 : ℝ) ≤ Real.exp (-2063/131072 : ℝ) ∧ Real.exp (-2063/131072 : ℝ) ≤ (984383776777/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123047972097/125000000000 : ℝ) ≤ (radius 8 (2063/16384 : ℝ)) ∧ (radius 8 (2063/16384 : ℝ)) ≤ (984383776777/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2063/16384 : ℝ)) (123047972097/125000000000 : ℝ) (984383776777/1000000000000 : ℝ) (8801786753/50000000000 : ℝ) (88017867533/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2063/16384 : ℝ)) (123047972097/125000000000 : ℝ) (984383776777/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123047972097/125000000000 : ℝ) (984383776777/1000000000000 : ℝ) (248047972097/250000000000 : ℝ) (992191888389/1000000000000 : ℝ) (496080582359/500000000000 : ℝ) (12402014559/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 1 (248047972097/250000000000 : ℝ) (992191888389/1000000000000 : ℝ) (496080582359/500000000000 : ℝ) (12402014559/12500000000 : ℝ) (992176526553/1000000000000 : ℝ) (198435305311/200000000000 : ℝ) (496088263217/500000000000 : ℝ) (248044131609/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 2 (992176526553/1000000000000 : ℝ) (198435305311/200000000000 : ℝ) (496088263217/500000000000 : ℝ) (248044131609/250000000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 3 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 4 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 5 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 6 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2063/16384 : ℝ)) 7 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2063/16384 : ℝ))) (8801786753/50000000000 : ℝ) (88017867533/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8801786753/50000000000 : ℝ) (88017867533/500000000000 : ℝ) (58801786753/100000000000 : ℝ) (588017867533/1000000000000 : ℝ) (419566127159/1000000000000 : ℝ) (6555720737/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 1 (58801786753/100000000000 : ℝ) (588017867533/1000000000000 : ℝ) (419566127159/1000000000000 : ℝ) (6555720737/15625000000 : ℝ) (15743499917/31250000000 : ℝ) (503791997351/1000000000000 : ℝ) (62087687409/125000000000 : ℝ) (6208768741/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 2 (15743499917/31250000000 : ℝ) (503791997351/1000000000000 : ℝ) (62087687409/125000000000 : ℝ) (6208768741/12500000000 : ℝ) (125061687077/250000000000 : ℝ) (125061687079/250000000000 : ℝ) (500234185559/1000000000000 : ℝ) (500234185567/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 3 (125061687077/250000000000 : ℝ) (125061687079/250000000000 : ℝ) (500234185559/1000000000000 : ℝ) (500234185567/1000000000000 : ℝ) (500240466933/1000000000000 : ℝ) (250120233471/500000000000 : ℝ) (250120233447/500000000000 : ℝ) (500240466903/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 4 (500240466933/1000000000000 : ℝ) (250120233471/500000000000 : ℝ) (250120233447/500000000000 : ℝ) (500240466903/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 5 (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 6 (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2063/16384 : ℝ))) 7 (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2063/16384 : ℝ)) hmem 8 (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2063/16384 : ℝ))) hcmem 8 (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2063/16384 : ℝ)) (992176526493/1000000000000 : ℝ) (31005516453/31250000000 : ℝ) (500240466913/1000000000000 : ℝ) (500240466923/1000000000000 : ℝ) (395985929397/500000000000 : ℝ) (791971858813/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0277_exp_lower
  have heNumeric : (410981321423/200000000000 : ℝ)/4 ≤ Real.exp (-21314046747641/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981321423/200000000000 : ℝ)/4 ≤ Real.exp ((16503/131072 : ℝ)-(791971858813/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16503/131072 : ℝ) (2063/16384 : ℝ) (791971858813/1000000000000 : ℝ) (410981321423/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0278; no trusted numerical premise.
theorem cover8_leaf0278_exp_radius : (499017192516140237/500000000000000000 : ℝ) ≤ Real.exp ((-16505/1048576 : ℝ)/8) ∧ Real.exp ((-16505/1048576 : ℝ)/8) ≤ (39921375401291219/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16505/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0278_exp_lower : (460056861758702133/500000000000000000 : ℝ) ≤ Real.exp ((-532851225981/800000000000 : ℝ)/8) ∧ Real.exp ((-532851225981/800000000000 : ℝ)/8) ≤ (920113723517404267/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532851225981/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0278_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453229979/500000000000 : ℝ) ≤ 4*Real.exp (2063/16384 : ℝ)*Real.exp (-mu (radius 8 (16505/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453229979/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16505/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0278_exp_radius
  have hrNumeric : (492191418997/500000000000 : ℝ) ≤ Real.exp (-16505/1048576 : ℝ) ∧ Real.exp (-16505/1048576 : ℝ) ≤ (196876567599/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492191418997/500000000000 : ℝ) ≤ (radius 8 (16505/131072 : ℝ)) ∧ (radius 8 (16505/131072 : ℝ)) ≤ (196876567599/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16505/131072 : ℝ)) (492191418997/500000000000 : ℝ) (196876567599/200000000000 : ℝ) (35208196921/200000000000 : ℝ) (44010246153/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16505/131072 : ℝ)) (492191418997/500000000000 : ℝ) (196876567599/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492191418997/500000000000 : ℝ) (196876567599/200000000000 : ℝ) (992191418997/1000000000000 : ℝ) (496095709499/500000000000 : ℝ) (992160691619/1000000000000 : ℝ) (49608034581/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 1 (992191418997/1000000000000 : ℝ) (496095709499/500000000000 : ℝ) (992160691619/1000000000000 : ℝ) (49608034581/50000000000 : ℝ) (248044013827/250000000000 : ℝ) (992176055309/1000000000000 : ℝ) (992176055189/1000000000000 : ℝ) (992176055191/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 2 (248044013827/250000000000 : ℝ) (992176055309/1000000000000 : ℝ) (992176055189/1000000000000 : ℝ) (992176055191/1000000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 3 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 4 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 5 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 6 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16505/131072 : ℝ)) 7 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16505/131072 : ℝ))) (35208196921/200000000000 : ℝ) (44010246153/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35208196921/200000000000 : ℝ) (44010246153/250000000000 : ℝ) (294010246151/500000000000 : ℝ) (294010246153/500000000000 : ℝ) (209786191517/500000000000 : ℝ) (419572383043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 1 (294010246151/500000000000 : ℝ) (294010246153/500000000000 : ℝ) (209786191517/500000000000 : ℝ) (419572383043/1000000000000 : ℝ) (125949109417/250000000000 : ℝ) (20151857507/40000000000 : ℝ) (496706310839/1000000000000 : ℝ) (496706310847/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 2 (125949109417/250000000000 : ℝ) (20151857507/40000000000 : ℝ) (496706310839/1000000000000 : ℝ) (496706310847/1000000000000 : ℝ) (500251374253/1000000000000 : ℝ) (500251374261/1000000000000 : ℝ) (62529851617/125000000000 : ℝ) (31264925809/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 3 (500251374253/1000000000000 : ℝ) (500251374261/1000000000000 : ℝ) (62529851617/125000000000 : ℝ) (31264925809/62500000000 : ℝ) (250122546797/500000000000 : ℝ) (500245093603/1000000000000 : ℝ) (100049018711/200000000000 : ℝ) (125061273391/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 4 (250122546797/500000000000 : ℝ) (500245093603/1000000000000 : ℝ) (100049018711/200000000000 : ℝ) (125061273391/250000000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 5 (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 6 (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16505/131072 : ℝ))) 7 (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16505/131072 : ℝ)) hmem 8 (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16505/131072 : ℝ))) hcmem 8 (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16505/131072 : ℝ)) (62011003453/62500000000 : ℝ) (3968704221/4000000000 : ℝ) (250122546787/500000000000 : ℝ) (31265318349/62500000000 : ℝ) (395989779901/500000000000 : ℝ) (39598977991/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0278_exp_lower
  have heNumeric : (1027453229979/500000000000 : ℝ)/4 ≤ Real.exp (-532851225981/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453229979/500000000000 : ℝ)/4 ≤ Real.exp ((2063/16384 : ℝ)-(39598977991/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2063/16384 : ℝ) (16505/131072 : ℝ) (39598977991/50000000000 : ℝ) (1027453229979/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0279; no trusted numerical premise.
theorem cover8_leaf0279_exp_radius : (998034266057317579/1000000000000000000 : ℝ) ≤ Real.exp ((-8253/524288 : ℝ)/8) ∧ Real.exp ((-8253/524288 : ℝ)/8) ≤ (49901713302865879/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8253/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0279_exp_lower : (460056857659166007/500000000000000000 : ℝ) ≤ Real.exp ((-21314051320439/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314051320439/32000000000000 : ℝ)/8) ≤ (184022743063666403/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314051320439/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0279_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906313469/1000000000000 : ℝ) ≤ 4*Real.exp (16505/131072 : ℝ)*Real.exp (-mu (radius 8 (8253/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906313469/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8253/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0279_exp_radius
  have hrNumeric : (492190949607/500000000000 : ℝ) ≤ Real.exp (-8253/524288 : ℝ) ∧ Real.exp (-8253/524288 : ℝ) ≤ (196876379843/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492190949607/500000000000 : ℝ) ≤ (radius 8 (8253/65536 : ℝ)) ∧ (radius 8 (8253/65536 : ℝ)) ≤ (196876379843/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8253/65536 : ℝ)) (492190949607/500000000000 : ℝ) (196876379843/200000000000 : ℝ) (88023116989/500000000000 : ℝ) (1375361203/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8253/65536 : ℝ)) (492190949607/500000000000 : ℝ) (196876379843/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492190949607/500000000000 : ℝ) (196876379843/200000000000 : ℝ) (992190949607/1000000000000 : ℝ) (124023868701/125000000000 : ℝ) (24804005463/25000000000 : ℝ) (992160218521/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 1 (992190949607/1000000000000 : ℝ) (124023868701/125000000000 : ℝ) (24804005463/25000000000 : ℝ) (992160218521/1000000000000 : ℝ) (992175584063/1000000000000 : ℝ) (198435116813/200000000000 : ℝ) (124021947993/125000000000 : ℝ) (496087791973/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 2 (992175584063/1000000000000 : ℝ) (198435116813/200000000000 : ℝ) (124021947993/125000000000 : ℝ) (496087791973/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 3 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 4 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 5 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 6 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8253/65536 : ℝ)) 7 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8253/65536 : ℝ))) (88023116989/500000000000 : ℝ) (1375361203/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88023116989/500000000000 : ℝ) (1375361203/7812500000 : ℝ) (588023116989/1000000000000 : ℝ) (9187861203/15625000000 : ℝ) (41957863861/100000000000 : ℝ) (209789319309/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 1 (588023116989/1000000000000 : ℝ) (9187861203/15625000000 : ℝ) (41957863861/100000000000 : ℝ) (209789319309/500000000000 : ℝ) (503800877799/1000000000000 : ℝ) (100760175561/200000000000 : ℝ) (24835556109/50000000000 : ℝ) (496711122187/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 2 (503800877799/1000000000000 : ℝ) (100760175561/200000000000 : ℝ) (24835556109/50000000000 : ℝ) (496711122187/1000000000000 : ℝ) (500255999989/1000000000000 : ℝ) (125063999999/250000000000 : ℝ) (500243440103/1000000000000 : ℝ) (500243440111/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 3 (500255999989/1000000000000 : ℝ) (125063999999/250000000000 : ℝ) (500243440103/1000000000000 : ℝ) (500243440111/1000000000000 : ℝ) (250124860023/500000000000 : ℝ) (250124860027/500000000000 : ℝ) (250124860003/500000000000 : ℝ) (100049944003/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 4 (250124860023/500000000000 : ℝ) (250124860027/500000000000 : ℝ) (250124860003/500000000000 : ℝ) (100049944003/200000000000 : ℝ) (250124860013/500000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 5 (250124860013/500000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 6 (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8253/65536 : ℝ))) 7 (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8253/65536 : ℝ)) hmem 8 (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8253/65536 : ℝ))) hcmem 8 (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8253/65536 : ℝ)) (992175584003/1000000000000 : ℝ) (496087792003/500000000000 : ℝ) (20009988801/40000000000 : ℝ) (100049944007/200000000000 : ℝ) (791987260483/1000000000000 : ℝ) (395993630251/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0279_exp_lower
  have heNumeric : (2054906313469/1000000000000 : ℝ)/4 ≤ Real.exp (-21314051320439/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906313469/1000000000000 : ℝ)/4 ≤ Real.exp ((16505/131072 : ℝ)-(395993630251/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16505/131072 : ℝ) (8253/65536 : ℝ) (395993630251/500000000000 : ℝ) (2054906313469/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0280; no trusted numerical premise.
theorem cover8_leaf0280_exp_radius : (499017073541184433/500000000000000000 : ℝ) ≤ Real.exp ((-16507/1048576 : ℝ)/8) ∧ Real.exp ((-16507/1048576 : ℝ)/8) ≤ (998034147082368867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16507/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0280_exp_lower : (46005685357785967/50000000000000000 : ℝ) ≤ Real.exp ((-10657026795747/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657026795747/16000000000000 : ℝ)/8) ≤ (920113707155719341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657026795747/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0280_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906167631/1000000000000 : ℝ) ≤ 4*Real.exp (8253/65536 : ℝ)*Real.exp (-mu (radius 8 (16507/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906167631/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16507/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0280_exp_radius
  have hrNumeric : (196876192087/200000000000 : ℝ) ≤ Real.exp (-16507/1048576 : ℝ) ∧ Real.exp (-16507/1048576 : ℝ) ≤ (246095240109/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196876192087/200000000000 : ℝ) ≤ (radius 8 (16507/131072 : ℝ)) ∧ (radius 8 (16507/131072 : ℝ)) ≤ (246095240109/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16507/131072 : ℝ)) (196876192087/200000000000 : ℝ) (246095240109/250000000000 : ℝ) (176051483183/1000000000000 : ℝ) (17605148319/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16507/131072 : ℝ)) (196876192087/200000000000 : ℝ) (246095240109/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196876192087/200000000000 : ℝ) (246095240109/250000000000 : ℝ) (992190480217/1000000000000 : ℝ) (496095240109/500000000000 : ℝ) (992159745421/1000000000000 : ℝ) (992159745423/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 1 (992190480217/1000000000000 : ℝ) (496095240109/500000000000 : ℝ) (992159745421/1000000000000 : ℝ) (992159745423/1000000000000 : ℝ) (992175112819/1000000000000 : ℝ) (992175112821/1000000000000 : ℝ) (992175112699/1000000000000 : ℝ) (496087556351/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 2 (992175112819/1000000000000 : ℝ) (992175112821/1000000000000 : ℝ) (992175112699/1000000000000 : ℝ) (496087556351/500000000000 : ℝ) (992175112759/1000000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 3 (992175112759/1000000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 4 (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 5 (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 6 (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16507/131072 : ℝ)) 7 (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16507/131072 : ℝ))) (176051483183/1000000000000 : ℝ) (17605148319/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176051483183/1000000000000 : ℝ) (17605148319/100000000000 : ℝ) (588025741591/1000000000000 : ℝ) (117605148319/200000000000 : ℝ) (104896223473/250000000000 : ℝ) (209792446951/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 1 (588025741591/1000000000000 : ℝ) (117605148319/200000000000 : ℝ) (104896223473/250000000000 : ℝ) (209792446951/500000000000 : ℝ) (503805317741/1000000000000 : ℝ) (503805317749/1000000000000 : ℝ) (496715933297/1000000000000 : ℝ) (99343186661/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 2 (503805317741/1000000000000 : ℝ) (503805317749/1000000000000 : ℝ) (496715933297/1000000000000 : ℝ) (99343186661/200000000000 : ℝ) (500260625519/1000000000000 : ℝ) (500260625527/1000000000000 : ℝ) (62531008383/125000000000 : ℝ) (500248067073/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 3 (500260625519/1000000000000 : ℝ) (500260625527/1000000000000 : ℝ) (62531008383/125000000000 : ℝ) (500248067073/1000000000000 : ℝ) (500254346291/1000000000000 : ℝ) (5002543463/10000000000 : ℝ) (125063586563/250000000000 : ℝ) (500254346261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 4 (500254346291/1000000000000 : ℝ) (5002543463/10000000000 : ℝ) (125063586563/250000000000 : ℝ) (500254346261/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 5 (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 6 (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16507/131072 : ℝ))) 7 (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16507/131072 : ℝ)) hmem 8 (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16507/131072 : ℝ))) hcmem 8 (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16507/131072 : ℝ)) (496087556379/500000000000 : ℝ) (496087556381/500000000000 : ℝ) (500254346271/1000000000000 : ℝ) (500254346281/1000000000000 : ℝ) (791994960847/1000000000000 : ℝ) (791994960867/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0280_exp_lower
  have heNumeric : (2054906167631/1000000000000 : ℝ)/4 ≤ Real.exp (-10657026795747/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906167631/1000000000000 : ℝ)/4 ≤ Real.exp ((8253/65536 : ℝ)-(791994960867/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8253/65536 : ℝ) (16507/131072 : ℝ) (791994960867/1000000000000 : ℝ) (2054906167631/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0281; no trusted numerical premise.
theorem cover8_leaf0281_exp_radius : (998034028107434337/1000000000000000000 : ℝ) ≤ Real.exp ((-4127/262144 : ℝ)/8) ∧ Real.exp ((-4127/262144 : ℝ)/8) ≤ (499017014053717169/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4127/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0281_exp_lower : (920113699029796273/1000000000000000000 : ℝ) ≤ Real.exp ((-21314055852341/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314055852341/32000000000000 : ℝ)/8) ≤ (460056849514898137/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314055852341/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0281_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906022449/1000000000000 : ℝ) ≤ 4*Real.exp (16507/131072 : ℝ)*Real.exp (-mu (radius 8 (4127/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906022449/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4127/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0281_exp_radius
  have hrNumeric : (984380021657/1000000000000 : ℝ) ≤ Real.exp (-4127/262144 : ℝ) ∧ Real.exp (-4127/262144 : ℝ) ≤ (492190010829/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984380021657/1000000000000 : ℝ) ≤ (radius 8 (4127/32768 : ℝ)) ∧ (radius 8 (4127/32768 : ℝ)) ≤ (492190010829/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4127/32768 : ℝ)) (984380021657/1000000000000 : ℝ) (492190010829/500000000000 : ℝ) (176056732221/1000000000000 : ℝ) (44014183057/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4127/32768 : ℝ)) (984380021657/1000000000000 : ℝ) (492190010829/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984380021657/1000000000000 : ℝ) (492190010829/500000000000 : ℝ) (248047502707/250000000000 : ℝ) (992190010829/1000000000000 : ℝ) (992159272323/1000000000000 : ℝ) (248039818081/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 1 (248047502707/250000000000 : ℝ) (992190010829/1000000000000 : ℝ) (992159272323/1000000000000 : ℝ) (248039818081/250000000000 : ℝ) (39686985663/40000000000 : ℝ) (992174641577/1000000000000 : ℝ) (62010915091/62500000000 : ℝ) (496087320729/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 2 (39686985663/40000000000 : ℝ) (992174641577/1000000000000 : ℝ) (62010915091/62500000000 : ℝ) (496087320729/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 3 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 4 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 5 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 6 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4127/32768 : ℝ)) 7 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4127/32768 : ℝ))) (176056732221/1000000000000 : ℝ) (44014183057/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176056732221/1000000000000 : ℝ) (44014183057/250000000000 : ℝ) (58802836611/100000000000 : ℝ) (294014183057/500000000000 : ℝ) (419591148883/1000000000000 : ℝ) (104897787223/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 1 (58802836611/100000000000 : ℝ) (294014183057/500000000000 : ℝ) (419591148883/1000000000000 : ℝ) (104897787223/250000000000 : ℝ) (62976219687/125000000000 : ℝ) (503809757503/1000000000000 : ℝ) (496720744193/1000000000000 : ℝ) (496720744201/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 2 (62976219687/125000000000 : ℝ) (503809757503/1000000000000 : ℝ) (496720744193/1000000000000 : ℝ) (496720744201/1000000000000 : ℝ) (125066312711/250000000000 : ℝ) (125066312713/250000000000 : ℝ) (25012634691/50000000000 : ℝ) (500252693829/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 3 (125066312711/250000000000 : ℝ) (125066312713/250000000000 : ℝ) (25012634691/50000000000 : ℝ) (500252693829/1000000000000 : ℝ) (125064743083/250000000000 : ℝ) (500258972341/1000000000000 : ℝ) (125064743073/250000000000 : ℝ) (250129486151/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 4 (125064743083/250000000000 : ℝ) (500258972341/1000000000000 : ℝ) (125064743073/250000000000 : ℝ) (250129486151/500000000000 : ℝ) (62532371539/125000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 5 (62532371539/125000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 6 (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4127/32768 : ℝ))) 7 (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4127/32768 : ℝ)) hmem 8 (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4127/32768 : ℝ))) hcmem 8 (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4127/32768 : ℝ)) (198434928303/200000000000 : ℝ) (496087320759/500000000000 : ℝ) (500258972311/1000000000000 : ℝ) (250129486161/500000000000 : ℝ) (198000665223/250000000000 : ℝ) (792002660913/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0281_exp_lower
  have heNumeric : (2054906022449/1000000000000 : ℝ)/4 ≤ Real.exp (-21314055852341/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906022449/1000000000000 : ℝ)/4 ≤ Real.exp ((16507/131072 : ℝ)-(792002660913/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16507/131072 : ℝ) (4127/32768 : ℝ) (792002660913/1000000000000 : ℝ) (2054906022449/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0282; no trusted numerical premise.
theorem cover8_leaf0282_exp_radius : (99803390913251399/100000000000000000 : ℝ) ≤ Real.exp ((-16509/1048576 : ℝ)/8) ∧ Real.exp ((-16509/1048576 : ℝ)/8) ≤ (998033909132513991/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16509/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0282_exp_lower : (230028422734853167/250000000000000000 : ℝ) ≤ Real.exp ((-213140581033/320000000000 : ℝ)/8) ∧ Real.exp ((-213140581033/320000000000 : ℝ)/8) ≤ (920113690939412669/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213140581033/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0282_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452938951/500000000000 : ℝ) ≤ 4*Real.exp (4127/32768 : ℝ)*Real.exp (-mu (radius 8 (16509/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452938951/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16509/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0282_exp_radius
  have hrNumeric : (984379082879/1000000000000 : ℝ) ≤ Real.exp (-16509/1048576 : ℝ) ∧ Real.exp (-16509/1048576 : ℝ) ≤ (1538092317/1562500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984379082879/1000000000000 : ℝ) ≤ (radius 8 (16509/131072 : ℝ)) ∧ (radius 8 (16509/131072 : ℝ)) ≤ (1538092317/1562500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16509/131072 : ℝ)) (984379082879/1000000000000 : ℝ) (1538092317/1562500000 : ℝ) (88030990549/500000000000 : ℝ) (35212396221/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16509/131072 : ℝ)) (984379082879/1000000000000 : ℝ) (1538092317/1562500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984379082879/1000000000000 : ℝ) (1538092317/1562500000 : ℝ) (992189541439/1000000000000 : ℝ) (3100592317/3125000000 : ℝ) (124019849903/125000000000 : ℝ) (496079399613/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 1 (992189541439/1000000000000 : ℝ) (3100592317/3125000000 : ℝ) (124019849903/125000000000 : ℝ) (496079399613/500000000000 : ℝ) (992174170331/1000000000000 : ℝ) (992174170333/1000000000000 : ℝ) (248043542553/250000000000 : ℝ) (496087085107/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 2 (992174170331/1000000000000 : ℝ) (992174170333/1000000000000 : ℝ) (248043542553/250000000000 : ℝ) (496087085107/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 3 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 4 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 5 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 6 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16509/131072 : ℝ)) 7 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16509/131072 : ℝ))) (88030990549/500000000000 : ℝ) (35212396221/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88030990549/500000000000 : ℝ) (35212396221/200000000000 : ℝ) (588030990549/1000000000000 : ℝ) (588030990553/1000000000000 : ℝ) (104899350897/250000000000 : ℝ) (419597403597/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 1 (588030990549/1000000000000 : ℝ) (588030990553/1000000000000 : ℝ) (104899350897/250000000000 : ℝ) (419597403597/1000000000000 : ℝ) (125953549267/250000000000 : ℝ) (20152567883/40000000000 : ℝ) (62090694359/125000000000 : ℝ) (1552267359/3125000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 2 (125953549267/250000000000 : ℝ) (20152567883/40000000000 : ℝ) (62090694359/125000000000 : ℝ) (1552267359/3125000000 : ℝ) (50026987597/100000000000 : ℝ) (250134937989/500000000000 : ℝ) (500257320377/1000000000000 : ℝ) (100051464077/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 3 (50026987597/100000000000 : ℝ) (250134937989/500000000000 : ℝ) (500257320377/1000000000000 : ℝ) (100051464077/200000000000 : ℝ) (500263598173/1000000000000 : ℝ) (250131799091/500000000000 : ℝ) (250131799067/500000000000 : ℝ) (500263598143/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 4 (500263598173/1000000000000 : ℝ) (250131799091/500000000000 : ℝ) (250131799067/500000000000 : ℝ) (500263598143/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 5 (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 6 (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16509/131072 : ℝ))) 7 (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16509/131072 : ℝ)) hmem 8 (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16509/131072 : ℝ))) hcmem 8 (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16509/131072 : ℝ)) (992174170271/1000000000000 : ℝ) (496087085137/500000000000 : ℝ) (500263598153/1000000000000 : ℝ) (500263598163/1000000000000 : ℝ) (792010360631/1000000000000 : ℝ) (15840207213/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0282_exp_lower
  have heNumeric : (1027452938951/500000000000 : ℝ)/4 ≤ Real.exp (-213140581033/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452938951/500000000000 : ℝ)/4 ≤ Real.exp ((4127/32768 : ℝ)-(15840207213/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4127/32768 : ℝ) (16509/131072 : ℝ) (15840207213/20000000000 : ℝ) (1027452938951/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0283; no trusted numerical premise.
theorem cover8_leaf0283_exp_radius : (499016895078803913/500000000000000000 : ℝ) ≤ Real.exp ((-8255/524288 : ℝ)/8) ∧ Real.exp ((-8255/524288 : ℝ)/8) ≤ (998033790157607827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8255/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0283_exp_lower : (230028420721429667/250000000000000000 : ℝ) ≤ Real.exp ((-21314060344051/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314060344051/32000000000000 : ℝ)/8) ≤ (920113682885718669/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314060344051/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0283_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490573401/100000000000 : ℝ) ≤ 4*Real.exp (16509/131072 : ℝ)*Real.exp (-mu (radius 8 (8255/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205490573401/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8255/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0283_exp_radius
  have hrNumeric : (492189072051/500000000000 : ℝ) ≤ Real.exp (-8255/524288 : ℝ) ∧ Real.exp (-8255/524288 : ℝ) ≤ (984378144103/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492189072051/500000000000 : ℝ) ≤ (radius 8 (8255/65536 : ℝ)) ∧ (radius 8 (8255/65536 : ℝ)) ≤ (984378144103/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8255/65536 : ℝ)) (492189072051/500000000000 : ℝ) (984378144103/1000000000000 : ℝ) (11004201863/62500000000 : ℝ) (88033614907/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8255/65536 : ℝ)) (492189072051/500000000000 : ℝ) (984378144103/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492189072051/500000000000 : ℝ) (984378144103/1000000000000 : ℝ) (992189072051/1000000000000 : ℝ) (248047268013/250000000000 : ℝ) (496079163063/500000000000 : ℝ) (992158326127/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 1 (992189072051/1000000000000 : ℝ) (248047268013/250000000000 : ℝ) (496079163063/500000000000 : ℝ) (992158326127/1000000000000 : ℝ) (62010856193/62500000000 : ℝ) (99217369909/100000000000 : ℝ) (992173698969/1000000000000 : ℝ) (992173698971/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 2 (62010856193/62500000000 : ℝ) (99217369909/100000000000 : ℝ) (992173698969/1000000000000 : ℝ) (992173698971/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 3 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 4 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 5 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 6 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8255/65536 : ℝ)) 7 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8255/65536 : ℝ))) (11004201863/62500000000 : ℝ) (88033614907/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11004201863/62500000000 : ℝ) (88033614907/500000000000 : ℝ) (73504201863/125000000000 : ℝ) (588033614907/1000000000000 : ℝ) (419603658001/1000000000000 : ℝ) (419603658009/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 1 (73504201863/125000000000 : ℝ) (588033614907/1000000000000 : ℝ) (419603658001/1000000000000 : ℝ) (419603658009/1000000000000 : ℝ) (125954659113/250000000000 : ℝ) (251909318229/500000000000 : ℝ) (49673036533/100000000000 : ℝ) (496730365337/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 2 (125954659113/250000000000 : ℝ) (251909318229/500000000000 : ℝ) (49673036533/100000000000 : ℝ) (496730365337/1000000000000 : ℝ) (500274500891/1000000000000 : ℝ) (250137250449/500000000000 : ℝ) (62532743341/125000000000 : ℝ) (31266371671/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 3 (500274500891/1000000000000 : ℝ) (250137250449/500000000000 : ℝ) (62532743341/125000000000 : ℝ) (31266371671/62500000000 : ℝ) (500268223809/1000000000000 : ℝ) (500268223817/1000000000000 : ℝ) (50026822377/100000000000 : ℝ) (250134111889/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 4 (500268223809/1000000000000 : ℝ) (500268223817/1000000000000 : ℝ) (50026822377/100000000000 : ℝ) (250134111889/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 5 (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 6 (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8255/65536 : ℝ))) 7 (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8255/65536 : ℝ)) hmem 8 (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8255/65536 : ℝ))) hcmem 8 (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8255/65536 : ℝ)) (248043424757/250000000000 : ℝ) (992173699031/1000000000000 : ℝ) (500268223789/1000000000000 : ℝ) (250134111899/500000000000 : ℝ) (15840361201/20000000000 : ℝ) (198004515017/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0283_exp_lower
  have heNumeric : (205490573401/100000000000 : ℝ)/4 ≤ Real.exp (-21314060344051/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490573401/100000000000 : ℝ)/4 ≤ Real.exp ((16509/131072 : ℝ)-(198004515017/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16509/131072 : ℝ) (8255/65536 : ℝ) (198004515017/250000000000 : ℝ) (205490573401/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0284; no trusted numerical premise.
theorem cover8_leaf0284_exp_radius : (199606734236543169/200000000000000000 : ℝ) ≤ Real.exp ((-16511/1048576 : ℝ)/8) ∧ Real.exp ((-16511/1048576 : ℝ)/8) ≤ (499016835591357923/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16511/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0284_exp_lower : (460056837434644671/500000000000000000 : ℝ) ≤ Real.exp ((-10657031287217/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657031287217/16000000000000 : ℝ)/8) ≤ (920113674869289343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657031287217/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0284_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2006743741/976562500 : ℝ) ≤ 4*Real.exp (8255/65536 : ℝ)*Real.exp (-mu (radius 8 (16511/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2006743741/976562500 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16511/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0284_exp_radius
  have hrNumeric : (984377205327/1000000000000 : ℝ) ≤ Real.exp (-16511/1048576 : ℝ) ∧ Real.exp (-16511/1048576 : ℝ) ≤ (61523575333/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984377205327/1000000000000 : ℝ) ≤ (radius 8 (16511/131072 : ℝ)) ∧ (radius 8 (16511/131072 : ℝ)) ≤ (61523575333/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16511/131072 : ℝ)) (984377205327/1000000000000 : ℝ) (61523575333/62500000000 : ℝ) (35214495669/200000000000 : ℝ) (176072478351/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16511/131072 : ℝ)) (984377205327/1000000000000 : ℝ) (61523575333/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984377205327/1000000000000 : ℝ) (61523575333/62500000000 : ℝ) (992188602663/1000000000000 : ℝ) (124023575333/125000000000 : ℝ) (248039463257/250000000000 : ℝ) (99215785303/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 1 (992188602663/1000000000000 : ℝ) (124023575333/125000000000 : ℝ) (248039463257/250000000000 : ℝ) (99215785303/100000000000 : ℝ) (198434645569/200000000000 : ℝ) (992173227847/1000000000000 : ℝ) (496086613863/500000000000 : ℝ) (62010826733/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 2 (198434645569/200000000000 : ℝ) (992173227847/1000000000000 : ℝ) (496086613863/500000000000 : ℝ) (62010826733/62500000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 3 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 4 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 5 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 6 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16511/131072 : ℝ)) 7 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16511/131072 : ℝ))) (35214495669/200000000000 : ℝ) (176072478351/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35214495669/200000000000 : ℝ) (176072478351/1000000000000 : ℝ) (147009059793/250000000000 : ℝ) (73504529897/125000000000 : ℝ) (209804956057/500000000000 : ℝ) (209804956061/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 1 (147009059793/250000000000 : ℝ) (73504529897/125000000000 : ℝ) (209804956057/500000000000 : ℝ) (209804956061/500000000000 : ℝ) (503823075643/1000000000000 : ℝ) (503823075649/1000000000000 : ℝ) (12418379389/25000000000 : ℝ) (496735175567/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 2 (503823075643/1000000000000 : ℝ) (503823075649/1000000000000 : ℝ) (12418379389/25000000000 : ℝ) (496735175567/1000000000000 : ℝ) (500279125601/1000000000000 : ℝ) (62534890701/125000000000 : ℝ) (500266572869/1000000000000 : ℝ) (500266572877/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 3 (500279125601/1000000000000 : ℝ) (62534890701/125000000000 : ℝ) (500266572869/1000000000000 : ℝ) (500266572877/1000000000000 : ℝ) (100054569847/200000000000 : ℝ) (500272849243/1000000000000 : ℝ) (100054569839/200000000000 : ℝ) (125068212301/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 4 (100054569847/200000000000 : ℝ) (500272849243/1000000000000 : ℝ) (100054569839/200000000000 : ℝ) (125068212301/250000000000 : ℝ) (100054569843/200000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 5 (100054569843/200000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 6 (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16511/131072 : ℝ))) 7 (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16511/131072 : ℝ)) hmem 8 (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16511/131072 : ℝ))) hcmem 8 (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16511/131072 : ℝ)) (198434645557/200000000000 : ℝ) (248043306947/250000000000 : ℝ) (250136424607/500000000000 : ℝ) (62534106153/125000000000 : ℝ) (792025759143/1000000000000 : ℝ) (396012879581/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0284_exp_lower
  have heNumeric : (2006743741/976562500 : ℝ)/4 ≤ Real.exp (-10657031287217/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2006743741/976562500 : ℝ)/4 ≤ Real.exp ((8255/65536 : ℝ)-(396012879581/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8255/65536 : ℝ) (16511/131072 : ℝ) (396012879581/500000000000 : ℝ) (2006743741/976562500 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0285; no trusted numerical premise.
theorem cover8_leaf0285_exp_radius : (998033552207838047/1000000000000000000 : ℝ) ≤ Real.exp ((-129/8192 : ℝ)/8) ∧ Real.exp ((-129/8192 : ℝ)/8) ≤ (31188548506494939/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-129/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0285_exp_lower : (92011366688851449/100000000000000000 : ℝ) ≤ Real.exp ((-21314064794897/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314064794897/32000000000000 : ℝ)/8) ≤ (920113666888514491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314064794897/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0285_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981089639/200000000000 : ℝ) ≤ 4*Real.exp (16511/131072 : ℝ)*Real.exp (-mu (radius 8 (129/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (410981089639/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (129/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0285_exp_radius
  have hrNumeric : (123047033319/125000000000 : ℝ) ≤ Real.exp (-129/8192 : ℝ) ∧ Real.exp (-129/8192 : ℝ) ≤ (984376266553/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123047033319/125000000000 : ℝ) ≤ (radius 8 (129/1024 : ℝ)) ∧ (radius 8 (129/1024 : ℝ)) ≤ (984376266553/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (129/1024 : ℝ)) (123047033319/125000000000 : ℝ) (984376266553/1000000000000 : ℝ) (34390181/195312500 : ℝ) (176077726727/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (129/1024 : ℝ)) (123047033319/125000000000 : ℝ) (984376266553/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (129/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123047033319/125000000000 : ℝ) (984376266553/1000000000000 : ℝ) (248047033319/250000000000 : ℝ) (992188133277/1000000000000 : ℝ) (992157379931/1000000000000 : ℝ) (248039344983/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (129/1024 : ℝ)) 1 (248047033319/250000000000 : ℝ) (992188133277/1000000000000 : ℝ) (992157379931/1000000000000 : ℝ) (248039344983/250000000000 : ℝ) (992172756603/1000000000000 : ℝ) (198434551321/200000000000 : ℝ) (248043189121/250000000000 : ℝ) (496086378243/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (129/1024 : ℝ)) 2 (992172756603/1000000000000 : ℝ) (198434551321/200000000000 : ℝ) (248043189121/250000000000 : ℝ) (496086378243/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (129/1024 : ℝ)) 3 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (129/1024 : ℝ)) 4 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (129/1024 : ℝ)) 5 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (129/1024 : ℝ)) 6 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (129/1024 : ℝ)) 7 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (129/1024 : ℝ))) (34390181/195312500 : ℝ) (176077726727/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (34390181/195312500 : ℝ) (176077726727/1000000000000 : ℝ) (229702681/390625000 : ℝ) (147009715841/250000000000 : ℝ) (209808082971/500000000000 : ℝ) (419616165951/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 1 (229702681/390625000 : ℝ) (147009715841/250000000000 : ℝ) (209808082971/500000000000 : ℝ) (419616165951/1000000000000 : ℝ) (503827514651/1000000000000 : ℝ) (251913757329/500000000000 : ℝ) (496739985573/1000000000000 : ℝ) (496739985581/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 2 (503827514651/1000000000000 : ℝ) (251913757329/500000000000 : ℝ) (496739985573/1000000000000 : ℝ) (496739985581/1000000000000 : ℝ) (15633867191/31250000000 : ℝ) (12507093753/25000000000 : ℝ) (50027119881/100000000000 : ℝ) (250135599409/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 3 (15633867191/31250000000 : ℝ) (12507093753/25000000000 : ℝ) (50027119881/100000000000 : ℝ) (250135599409/500000000000 : ℝ) (500277474461/1000000000000 : ℝ) (500277474469/1000000000000 : ℝ) (500277474421/1000000000000 : ℝ) (50027747443/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 4 (500277474461/1000000000000 : ℝ) (500277474469/1000000000000 : ℝ) (500277474421/1000000000000 : ℝ) (50027747443/100000000000 : ℝ) (500277474441/1000000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 5 (500277474441/1000000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 6 (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (129/1024 : ℝ))) 7 (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (129/1024 : ℝ)) hmem 8 (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (129/1024 : ℝ))) hcmem 8 (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (129/1024 : ℝ)) (992172756543/1000000000000 : ℝ) (496086378273/500000000000 : ℝ) (12506936861/25000000000 : ℝ) (10005549489/20000000000 : ℝ) (792033457927/1000000000000 : ℝ) (396016728973/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0285_exp_lower
  have heNumeric : (410981089639/200000000000 : ℝ)/4 ≤ Real.exp (-21314064794897/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981089639/200000000000 : ℝ)/4 ≤ Real.exp ((16511/131072 : ℝ)-(396016728973/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16511/131072 : ℝ) (129/1024 : ℝ) (396016728973/500000000000 : ℝ) (410981089639/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0286; no trusted numerical premise.
theorem cover8_leaf0286_exp_radius : (31188544788530451/31250000000000000 : ℝ) ≤ Real.exp ((-16513/1048576 : ℝ)/8) ∧ Real.exp ((-16513/1048576 : ℝ)/8) ≤ (998033433232974433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16513/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0286_exp_lower : (460056829472042099/500000000000000000 : ℝ) ≤ Real.exp ((-333032296957/500000000000 : ℝ)/8) ∧ Real.exp ((-333032296957/500000000000 : ℝ)/8) ≤ (920113658944084199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333032296957/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0286_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431581641/62500000000 : ℝ) ≤ 4*Real.exp (129/1024 : ℝ)*Real.exp (-mu (radius 8 (16513/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (128431581641/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16513/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0286_exp_radius
  have hrNumeric : (492187663889/500000000000 : ℝ) ≤ Real.exp (-16513/1048576 : ℝ) ∧ Real.exp (-16513/1048576 : ℝ) ≤ (984375327779/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492187663889/500000000000 : ℝ) ≤ (radius 8 (16513/131072 : ℝ)) ∧ (radius 8 (16513/131072 : ℝ)) ≤ (984375327779/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16513/131072 : ℝ)) (492187663889/500000000000 : ℝ) (984375327779/1000000000000 : ℝ) (176082974929/1000000000000 : ℝ) (35216594987/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16513/131072 : ℝ)) (492187663889/500000000000 : ℝ) (984375327779/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492187663889/500000000000 : ℝ) (984375327779/1000000000000 : ℝ) (992187663889/1000000000000 : ℝ) (99218766389/100000000000 : ℝ) (992156906833/1000000000000 : ℝ) (198431381367/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 1 (992187663889/1000000000000 : ℝ) (99218766389/100000000000 : ℝ) (992156906833/1000000000000 : ℝ) (198431381367/200000000000 : ℝ) (992172285361/1000000000000 : ℝ) (992172285363/1000000000000 : ℝ) (992172285241/1000000000000 : ℝ) (248043071311/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 2 (992172285361/1000000000000 : ℝ) (992172285363/1000000000000 : ℝ) (992172285241/1000000000000 : ℝ) (248043071311/250000000000 : ℝ) (992172285301/1000000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 3 (992172285301/1000000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 4 (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 5 (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 6 (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16513/131072 : ℝ)) 7 (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16513/131072 : ℝ))) (176082974929/1000000000000 : ℝ) (35216594987/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176082974929/1000000000000 : ℝ) (35216594987/200000000000 : ℝ) (73505185933/125000000000 : ℝ) (147010371867/250000000000 : ℝ) (209811209739/500000000000 : ℝ) (209811209743/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 1 (73505185933/125000000000 : ℝ) (147010371867/250000000000 : ℝ) (209811209739/500000000000 : ℝ) (209811209743/500000000000 : ℝ) (503831953471/1000000000000 : ℝ) (503831953477/1000000000000 : ℝ) (99348959073/200000000000 : ℝ) (496744795373/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 2 (503831953471/1000000000000 : ℝ) (503831953477/1000000000000 : ℝ) (99348959073/200000000000 : ℝ) (496744795373/1000000000000 : ℝ) (250144187209/500000000000 : ℝ) (20011534977/40000000000 : ℝ) (250137912273/500000000000 : ℝ) (250137912277/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 3 (250144187209/500000000000 : ℝ) (20011534977/40000000000 : ℝ) (250137912273/500000000000 : ℝ) (250137912277/500000000000 : ℝ) (250141049741/500000000000 : ℝ) (50028209949/100000000000 : ℝ) (250141049721/500000000000 : ℝ) (500282099451/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 4 (250141049741/500000000000 : ℝ) (50028209949/100000000000 : ℝ) (250141049721/500000000000 : ℝ) (500282099451/1000000000000 : ℝ) (250141049731/500000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 5 (250141049731/500000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 6 (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16513/131072 : ℝ))) 7 (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16513/131072 : ℝ)) hmem 8 (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16513/131072 : ℝ))) hcmem 8 (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16513/131072 : ℝ)) (9921722853/10000000000 : ℝ) (124021535663/125000000000 : ℝ) (500282099461/1000000000000 : ℝ) (500282099471/1000000000000 : ℝ) (396020578197/500000000000 : ℝ) (396020578207/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0286_exp_lower
  have heNumeric : (128431581641/62500000000 : ℝ)/4 ≤ Real.exp (-333032296957/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431581641/62500000000 : ℝ)/4 ≤ Real.exp ((129/1024 : ℝ)-(396020578207/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (129/1024 : ℝ) (16513/131072 : ℝ) (396020578207/500000000000 : ℝ) (128431581641/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0287; no trusted numerical premise.
theorem cover8_leaf0287_exp_radius : (1596853302813/1600000000000 : ℝ) ≤ Real.exp ((-8257/524288 : ℝ)/8) ∧ Real.exp ((-8257/524288 : ℝ)/8) ≤ (998033314258125001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8257/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0287_exp_lower : (184022730207268701/200000000000000000 : ℝ) ≤ Real.exp ((-21314069205391/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314069205391/32000000000000 : ℝ)/8) ≤ (460056825518171753/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314069205391/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0287_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726291243/250000000000 : ℝ) ≤ 4*Real.exp (16513/131072 : ℝ)*Real.exp (-mu (radius 8 (8257/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726291243/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8257/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0287_exp_radius
  have hrNumeric : (196874877801/200000000000 : ℝ) ≤ Real.exp (-8257/524288 : ℝ) ∧ Real.exp (-8257/524288 : ℝ) ≤ (492187194503/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196874877801/200000000000 : ℝ) ≤ (radius 8 (8257/65536 : ℝ)) ∧ (radius 8 (8257/65536 : ℝ)) ≤ (492187194503/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8257/65536 : ℝ)) (196874877801/200000000000 : ℝ) (492187194503/500000000000 : ℝ) (17608822297/100000000000 : ℝ) (176088222977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8257/65536 : ℝ)) (196874877801/200000000000 : ℝ) (492187194503/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196874877801/200000000000 : ℝ) (492187194503/500000000000 : ℝ) (496093597251/500000000000 : ℝ) (992187194503/1000000000000 : ℝ) (124019554217/125000000000 : ℝ) (496078216869/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 1 (496093597251/500000000000 : ℝ) (992187194503/1000000000000 : ℝ) (124019554217/125000000000 : ℝ) (496078216869/500000000000 : ℝ) (992171814119/1000000000000 : ℝ) (992171814121/1000000000000 : ℝ) (992171813999/1000000000000 : ℝ) (496085907001/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 2 (992171814119/1000000000000 : ℝ) (992171814121/1000000000000 : ℝ) (992171813999/1000000000000 : ℝ) (496085907001/500000000000 : ℝ) (992171814059/1000000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 3 (992171814059/1000000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 4 (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 5 (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 6 (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8257/65536 : ℝ)) 7 (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8257/65536 : ℝ))) (17608822297/100000000000 : ℝ) (176088222977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17608822297/100000000000 : ℝ) (176088222977/1000000000000 : ℝ) (117608822297/200000000000 : ℝ) (588044111489/1000000000000 : ℝ) (419628672721/1000000000000 : ℝ) (41962867273/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 1 (117608822297/200000000000 : ℝ) (588044111489/1000000000000 : ℝ) (419628672721/1000000000000 : ℝ) (41962867273/100000000000 : ℝ) (503836392103/1000000000000 : ℝ) (50383639211/100000000000 : ℝ) (99349920987/200000000000 : ℝ) (496749604943/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 2 (503836392103/1000000000000 : ℝ) (50383639211/100000000000 : ℝ) (99349920987/200000000000 : ℝ) (496749604943/1000000000000 : ℝ) (500292998519/1000000000000 : ℝ) (500292998527/1000000000000 : ℝ) (125070112519/250000000000 : ℝ) (100056090017/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 3 (500292998519/1000000000000 : ℝ) (500292998527/1000000000000 : ℝ) (125070112519/250000000000 : ℝ) (100056090017/200000000000 : ℝ) (500286724297/1000000000000 : ℝ) (250143362153/500000000000 : ℝ) (250143362129/500000000000 : ℝ) (500286724267/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 4 (500286724297/1000000000000 : ℝ) (250143362153/500000000000 : ℝ) (250143362129/500000000000 : ℝ) (500286724267/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 5 (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 6 (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8257/65536 : ℝ))) 7 (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8257/65536 : ℝ)) hmem 8 (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8257/65536 : ℝ))) hcmem 8 (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8257/65536 : ℝ)) (496085907029/500000000000 : ℝ) (496085907031/500000000000 : ℝ) (500286724277/1000000000000 : ℝ) (500286724287/1000000000000 : ℝ) (792048854543/1000000000000 : ℝ) (792048854563/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0287_exp_lower
  have heNumeric : (513726291243/250000000000 : ℝ)/4 ≤ Real.exp (-21314069205391/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726291243/250000000000 : ℝ)/4 ≤ Real.exp ((16513/131072 : ℝ)-(792048854563/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16513/131072 : ℝ) (8257/65536 : ℝ) (792048854563/1000000000000 : ℝ) (513726291243/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0288; no trusted numerical premise.
theorem cover8_leaf0288_exp_radius : (998033195283289751/1000000000000000000 : ℝ) ≤ Real.exp ((-16515/1048576 : ℝ)/8) ∧ Real.exp ((-16515/1048576 : ℝ)/8) ≤ (124754149410411219/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16515/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0288_exp_lower : (57507102697816399/62500000000000000 : ℝ) ≤ Real.exp ((-2131407139539/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131407139539/3200000000000 : ℝ)/8) ≤ (184022728633012477/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131407139539/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0288_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905024339/1000000000000 : ℝ) ≤ 4*Real.exp (8257/65536 : ℝ)*Real.exp (-mu (radius 8 (16515/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905024339/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16515/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0288_exp_radius
  have hrNumeric : (984373450233/1000000000000 : ℝ) ≤ Real.exp (-16515/1048576 : ℝ) ∧ Real.exp (-16515/1048576 : ℝ) ≤ (492186725117/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984373450233/1000000000000 : ℝ) ≤ (radius 8 (16515/131072 : ℝ)) ∧ (radius 8 (16515/131072 : ℝ)) ≤ (492186725117/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16515/131072 : ℝ)) (984373450233/1000000000000 : ℝ) (492186725117/500000000000 : ℝ) (35218694169/200000000000 : ℝ) (44023367713/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16515/131072 : ℝ)) (984373450233/1000000000000 : ℝ) (492186725117/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984373450233/1000000000000 : ℝ) (492186725117/500000000000 : ℝ) (248046681279/250000000000 : ℝ) (992186725117/1000000000000 : ℝ) (992155960639/1000000000000 : ℝ) (992155960641/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 1 (248046681279/250000000000 : ℝ) (992186725117/1000000000000 : ℝ) (992155960639/1000000000000 : ℝ) (992155960641/1000000000000 : ℝ) (992171342877/1000000000000 : ℝ) (992171342879/1000000000000 : ℝ) (496085671379/500000000000 : ℝ) (24804283569/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 2 (992171342877/1000000000000 : ℝ) (992171342879/1000000000000 : ℝ) (496085671379/500000000000 : ℝ) (24804283569/25000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 3 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 4 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 5 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 6 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16515/131072 : ℝ)) 7 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16515/131072 : ℝ))) (35218694169/200000000000 : ℝ) (44023367713/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35218694169/200000000000 : ℝ) (44023367713/250000000000 : ℝ) (294023367711/500000000000 : ℝ) (294023367713/500000000000 : ℝ) (419634925673/1000000000000 : ℝ) (209817462841/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 1 (294023367711/500000000000 : ℝ) (294023367713/500000000000 : ℝ) (419634925673/1000000000000 : ℝ) (209817462841/500000000000 : ℝ) (503840830547/1000000000000 : ℝ) (251920415277/500000000000 : ℝ) (124188603571/250000000000 : ℝ) (124188603573/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 2 (503840830547/1000000000000 : ℝ) (251920415277/500000000000 : ℝ) (124188603571/250000000000 : ℝ) (124188603573/250000000000 : ℝ) (100059524483/200000000000 : ℝ) (500297622423/1000000000000 : ℝ) (250142537701/500000000000 : ℝ) (500285075411/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 3 (100059524483/200000000000 : ℝ) (500297622423/1000000000000 : ℝ) (250142537701/500000000000 : ℝ) (500285075411/1000000000000 : ℝ) (125072837227/250000000000 : ℝ) (500291348917/1000000000000 : ℝ) (500291348869/1000000000000 : ℝ) (250145674439/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 4 (125072837227/250000000000 : ℝ) (500291348917/1000000000000 : ℝ) (500291348869/1000000000000 : ℝ) (250145674439/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 5 (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 6 (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16515/131072 : ℝ))) 7 (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16515/131072 : ℝ)) hmem 8 (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16515/131072 : ℝ))) hcmem 8 (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16515/131072 : ℝ)) (992171342817/1000000000000 : ℝ) (49608567141/50000000000 : ℝ) (62536418611/125000000000 : ℝ) (250145674449/500000000000 : ℝ) (99007069047/125000000000 : ℝ) (158411310479/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0288_exp_lower
  have heNumeric : (2054905024339/1000000000000 : ℝ)/4 ≤ Real.exp (-2131407139539/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905024339/1000000000000 : ℝ)/4 ≤ Real.exp ((8257/65536 : ℝ)-(158411310479/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8257/65536 : ℝ) (16515/131072 : ℝ) (158411310479/200000000000 : ℝ) (2054905024339/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0289; no trusted numerical premise.
theorem cover8_leaf0289_exp_radius : (249508269077117171/250000000000000000 : ℝ) ≤ Real.exp ((-4129/262144 : ℝ)/8) ∧ Real.exp ((-4129/262144 : ℝ)/8) ≤ (199606615261693737/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4129/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0289_exp_lower : (920113635330125819/1000000000000000000 : ℝ) ≤ Real.exp ((-21314073575277/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314073575277/32000000000000 : ℝ)/8) ≤ (46005681766506291/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314073575277/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0289_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726221089/250000000000 : ℝ) ≤ 4*Real.exp (16515/131072 : ℝ)*Real.exp (-mu (radius 8 (4129/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513726221089/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4129/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0289_exp_radius
  have hrNumeric : (492186255731/500000000000 : ℝ) ≤ Real.exp (-4129/262144 : ℝ) ∧ Real.exp (-4129/262144 : ℝ) ≤ (984372511463/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492186255731/500000000000 : ℝ) ≤ (radius 8 (4129/32768 : ℝ)) ∧ (radius 8 (4129/32768 : ℝ)) ≤ (984372511463/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4129/32768 : ℝ)) (492186255731/500000000000 : ℝ) (984372511463/1000000000000 : ℝ) (176098718553/1000000000000 : ℝ) (176098718559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4129/32768 : ℝ)) (492186255731/500000000000 : ℝ) (984372511463/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492186255731/500000000000 : ℝ) (984372511463/1000000000000 : ℝ) (992186255731/1000000000000 : ℝ) (248046563933/250000000000 : ℝ) (992155487543/1000000000000 : ℝ) (124019435943/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 1 (992186255731/1000000000000 : ℝ) (248046563933/250000000000 : ℝ) (992155487543/1000000000000 : ℝ) (124019435943/125000000000 : ℝ) (992170871637/1000000000000 : ℝ) (496085435819/500000000000 : ℝ) (992170871517/1000000000000 : ℝ) (992170871519/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 2 (992170871637/1000000000000 : ℝ) (496085435819/500000000000 : ℝ) (992170871517/1000000000000 : ℝ) (992170871519/1000000000000 : ℝ) (992170871577/1000000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 3 (992170871577/1000000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 4 (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 5 (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 6 (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4129/32768 : ℝ)) 7 (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4129/32768 : ℝ))) (176098718553/1000000000000 : ℝ) (176098718559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176098718553/1000000000000 : ℝ) (176098718559/1000000000000 : ℝ) (147012339819/250000000000 : ℝ) (7350616991/12500000000 : ℝ) (419641178333/1000000000000 : ℝ) (419641178341/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 1 (147012339819/250000000000 : ℝ) (7350616991/12500000000 : ℝ) (419641178333/1000000000000 : ℝ) (419641178341/1000000000000 : ℝ) (125961317201/250000000000 : ℝ) (503845268811/1000000000000 : ℝ) (496759223411/1000000000000 : ℝ) (496759223419/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 2 (125961317201/250000000000 : ℝ) (503845268811/1000000000000 : ℝ) (496759223411/1000000000000 : ℝ) (496759223419/1000000000000 : ℝ) (500302246107/1000000000000 : ℝ) (100060449223/200000000000 : ℝ) (500289700523/1000000000000 : ℝ) (125072425133/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 3 (500302246107/1000000000000 : ℝ) (100060449223/200000000000 : ℝ) (500289700523/1000000000000 : ℝ) (125072425133/250000000000 : ℝ) (100059194663/200000000000 : ℝ) (125073993331/250000000000 : ℝ) (20011838931/40000000000 : ℝ) (100059194657/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 4 (100059194663/200000000000 : ℝ) (125073993331/250000000000 : ℝ) (20011838931/40000000000 : ℝ) (100059194657/200000000000 : ℝ) (100059194659/200000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 5 (100059194659/200000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 6 (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4129/32768 : ℝ))) 7 (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4129/32768 : ℝ)) hmem 8 (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4129/32768 : ℝ))) hcmem 8 (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4129/32768 : ℝ)) (124021358947/125000000000 : ℝ) (992170871579/1000000000000 : ℝ) (250147986647/500000000000 : ℝ) (100059194661/200000000000 : ℝ) (79206424989/100000000000 : ℝ) (792064249911/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0289_exp_lower
  have heNumeric : (513726221089/250000000000 : ℝ)/4 ≤ Real.exp (-21314073575277/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726221089/250000000000 : ℝ)/4 ≤ Real.exp ((16515/131072 : ℝ)-(792064249911/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16515/131072 : ℝ) (4129/32768 : ℝ) (792064249911/1000000000000 : ℝ) (513726221089/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0290; no trusted numerical premise.
theorem cover8_leaf0290_exp_radius : (998032957333661801/1000000000000000000 : ℝ) ≤ Real.exp ((-16517/1048576 : ℝ)/8) ∧ Real.exp ((-16517/1048576 : ℝ)/8) ≤ (499016478666830901/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16517/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0290_exp_lower : (460056813765479369/500000000000000000 : ℝ) ≤ Real.exp ((-5328518936303/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328518936303/8000000000000 : ℝ)/8) ≤ (920113627530958739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328518936303/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0290_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726186253/250000000000 : ℝ) ≤ 4*Real.exp (4129/32768 : ℝ)*Real.exp (-mu (radius 8 (16517/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726186253/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16517/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0290_exp_radius
  have hrNumeric : (984371572691/1000000000000 : ℝ) ≤ Real.exp (-16517/1048576 : ℝ) ∧ Real.exp (-16517/1048576 : ℝ) ≤ (246092893173/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984371572691/1000000000000 : ℝ) ≤ (radius 8 (16517/131072 : ℝ)) ∧ (radius 8 (16517/131072 : ℝ)) ≤ (246092893173/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16517/131072 : ℝ)) (984371572691/1000000000000 : ℝ) (246092893173/250000000000 : ℝ) (176103966099/1000000000000 : ℝ) (35220793221/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16517/131072 : ℝ)) (984371572691/1000000000000 : ℝ) (246092893173/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984371572691/1000000000000 : ℝ) (246092893173/250000000000 : ℝ) (198437157269/200000000000 : ℝ) (496092893173/500000000000 : ℝ) (496077507223/500000000000 : ℝ) (992155014447/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 1 (198437157269/200000000000 : ℝ) (496092893173/500000000000 : ℝ) (496077507223/500000000000 : ℝ) (992155014447/1000000000000 : ℝ) (198434080079/200000000000 : ℝ) (992170400397/1000000000000 : ℝ) (248042600069/250000000000 : ℝ) (496085200139/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 2 (198434080079/200000000000 : ℝ) (992170400397/1000000000000 : ℝ) (248042600069/250000000000 : ℝ) (496085200139/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 3 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 4 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 5 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 6 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16517/131072 : ℝ)) 7 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16517/131072 : ℝ))) (176103966099/1000000000000 : ℝ) (35220793221/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176103966099/1000000000000 : ℝ) (35220793221/200000000000 : ℝ) (588051983049/1000000000000 : ℝ) (588051983053/1000000000000 : ℝ) (419647430707/1000000000000 : ℝ) (83929486143/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 1 (588051983049/1000000000000 : ℝ) (588051983053/1000000000000 : ℝ) (419647430707/1000000000000 : ℝ) (83929486143/200000000000 : ℝ) (251924853439/500000000000 : ℝ) (125962426721/250000000000 : ℝ) (496764032321/1000000000000 : ℝ) (496764032329/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 2 (251924853439/500000000000 : ℝ) (125962426721/250000000000 : ℝ) (496764032321/1000000000000 : ℝ) (496764032329/1000000000000 : ℝ) (500306869599/1000000000000 : ℝ) (500306869607/1000000000000 : ℝ) (100058865089/200000000000 : ℝ) (500294325453/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 3 (500306869599/1000000000000 : ℝ) (500306869607/1000000000000 : ℝ) (100058865089/200000000000 : ℝ) (500294325453/1000000000000 : ℝ) (250150298761/500000000000 : ℝ) (50030059753/100000000000 : ℝ) (250150298741/500000000000 : ℝ) (500300597491/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 4 (250150298761/500000000000 : ℝ) (50030059753/100000000000 : ℝ) (250150298741/500000000000 : ℝ) (500300597491/1000000000000 : ℝ) (250150298751/500000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 5 (250150298751/500000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 6 (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16517/131072 : ℝ))) 7 (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16517/131072 : ℝ)) hmem 8 (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16517/131072 : ℝ))) hcmem 8 (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16517/131072 : ℝ)) (198434080067/200000000000 : ℝ) (496085200169/500000000000 : ℝ) (500300597501/1000000000000 : ℝ) (500300597511/1000000000000 : ℝ) (792071947097/1000000000000 : ℝ) (198017986779/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0290_exp_lower
  have heNumeric : (513726186253/250000000000 : ℝ)/4 ≤ Real.exp (-5328518936303/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726186253/250000000000 : ℝ)/4 ≤ Real.exp ((4129/32768 : ℝ)-(198017986779/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4129/32768 : ℝ) (16517/131072 : ℝ) (198017986779/250000000000 : ℝ) (513726186253/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0291; no trusted numerical premise.
theorem cover8_leaf0291_exp_radius : (9980328383588691/10000000000000000 : ℝ) ≤ Real.exp ((-8259/524288 : ℝ)/8) ∧ Real.exp ((-8259/524288 : ℝ)/8) ≤ (998032838358869101/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8259/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0291_exp_lower : (57507101235580397/62500000000000000 : ℝ) ≤ Real.exp ((-4262815580943/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262815580943/6400000000000 : ℝ)/8) ≤ (920113619769286353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262815580943/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0291_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452303169/500000000000 : ℝ) ≤ 4*Real.exp (16517/131072 : ℝ)*Real.exp (-mu (radius 8 (8259/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452303169/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8259/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0291_exp_radius
  have hrNumeric : (492185316961/500000000000 : ℝ) ≤ Real.exp (-8259/524288 : ℝ) ∧ Real.exp (-8259/524288 : ℝ) ≤ (984370633923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492185316961/500000000000 : ℝ) ≤ (radius 8 (8259/65536 : ℝ)) ∧ (radius 8 (8259/65536 : ℝ)) ≤ (984370633923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8259/65536 : ℝ)) (492185316961/500000000000 : ℝ) (984370633923/1000000000000 : ℝ) (5503412921/31250000000 : ℝ) (176109213479/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8259/65536 : ℝ)) (492185316961/500000000000 : ℝ) (984370633923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492185316961/500000000000 : ℝ) (984370633923/1000000000000 : ℝ) (992185316961/1000000000000 : ℝ) (496092658481/500000000000 : ℝ) (19843090827/20000000000 : ℝ) (992154541351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 1 (992185316961/1000000000000 : ℝ) (496092658481/500000000000 : ℝ) (19843090827/20000000000 : ℝ) (992154541351/1000000000000 : ℝ) (198433985831/200000000000 : ℝ) (992169929157/1000000000000 : ℝ) (248042482259/250000000000 : ℝ) (496084964519/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 2 (198433985831/200000000000 : ℝ) (992169929157/1000000000000 : ℝ) (248042482259/250000000000 : ℝ) (496084964519/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 3 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 4 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 5 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 6 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8259/65536 : ℝ)) 7 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8259/65536 : ℝ))) (5503412921/31250000000 : ℝ) (176109213479/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5503412921/31250000000 : ℝ) (176109213479/1000000000000 : ℝ) (36753412921/62500000000 : ℝ) (29402730337/50000000000 : ℝ) (419653682781/1000000000000 : ℝ) (41965368279/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 1 (36753412921/62500000000 : ℝ) (29402730337/50000000000 : ℝ) (419653682781/1000000000000 : ℝ) (41965368279/100000000000 : ℝ) (251927072379/500000000000 : ℝ) (100770828953/200000000000 : ℝ) (124192210251/250000000000 : ℝ) (124192210253/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 2 (251927072379/500000000000 : ℝ) (100770828953/200000000000 : ℝ) (124192210251/250000000000 : ℝ) (124192210253/250000000000 : ℝ) (500311492881/1000000000000 : ℝ) (500311492889/1000000000000 : ℝ) (100059790031/200000000000 : ℝ) (500298950163/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 3 (500311492881/1000000000000 : ℝ) (500311492889/1000000000000 : ℝ) (100059790031/200000000000 : ℝ) (500298950163/1000000000000 : ℝ) (250152610759/500000000000 : ℝ) (250152610763/500000000000 : ℝ) (250152610739/500000000000 : ℝ) (500305221487/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 4 (250152610759/500000000000 : ℝ) (250152610763/500000000000 : ℝ) (250152610739/500000000000 : ℝ) (500305221487/1000000000000 : ℝ) (250152610749/500000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 5 (250152610749/500000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 6 (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8259/65536 : ℝ))) 7 (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8259/65536 : ℝ)) hmem 8 (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8259/65536 : ℝ))) hcmem 8 (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8259/65536 : ℝ)) (198433985819/200000000000 : ℝ) (496084964549/500000000000 : ℝ) (500305221497/1000000000000 : ℝ) (500305221507/1000000000000 : ℝ) (99009955497/125000000000 : ℝ) (158415928799/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0291_exp_lower
  have heNumeric : (1027452303169/500000000000 : ℝ)/4 ≤ Real.exp (-4262815580943/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452303169/500000000000 : ℝ)/4 ≤ Real.exp ((16517/131072 : ℝ)-(158415928799/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16517/131072 : ℝ) (8259/65536 : ℝ) (158415928799/200000000000 : ℝ) (1027452303169/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0292; no trusted numerical premise.
theorem cover8_leaf0292_exp_radius : (998032719384090583/1000000000000000000 : ℝ) ≤ Real.exp ((-16519/1048576 : ℝ)/8) ∧ Real.exp ((-16519/1048576 : ℝ)/8) ≤ (124754089923011323/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16519/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0292_exp_lower : (7188387594085339/7812500000000000 : ℝ) ≤ Real.exp ((-10657040027197/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657040027197/16000000000000 : ℝ)/8) ≤ (920113612042923393/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657040027197/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0292_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980893659/200000000000 : ℝ) ≤ 4*Real.exp (8259/65536 : ℝ)*Real.exp (-mu (radius 8 (16519/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980893659/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16519/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0292_exp_radius
  have hrNumeric : (984369695153/1000000000000 : ℝ) ≤ Real.exp (-16519/1048576 : ℝ) ∧ Real.exp (-16519/1048576 : ℝ) ≤ (492184847577/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984369695153/1000000000000 : ℝ) ≤ (radius 8 (16519/131072 : ℝ)) ∧ (radius 8 (16519/131072 : ℝ)) ≤ (492184847577/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16519/131072 : ℝ)) (984369695153/1000000000000 : ℝ) (492184847577/500000000000 : ℝ) (35222892137/200000000000 : ℝ) (176114460691/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16519/131072 : ℝ)) (984369695153/1000000000000 : ℝ) (492184847577/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984369695153/1000000000000 : ℝ) (492184847577/500000000000 : ℝ) (124023105947/125000000000 : ℝ) (992184847577/1000000000000 : ℝ) (496077034127/500000000000 : ℝ) (198430813651/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 1 (124023105947/125000000000 : ℝ) (992184847577/1000000000000 : ℝ) (496077034127/500000000000 : ℝ) (198430813651/200000000000 : ℝ) (198433891583/200000000000 : ℝ) (248042364479/250000000000 : ℝ) (198433891559/200000000000 : ℝ) (992169457797/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 2 (198433891583/200000000000 : ℝ) (248042364479/250000000000 : ℝ) (198433891559/200000000000 : ℝ) (992169457797/1000000000000 : ℝ) (198433891571/200000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 3 (198433891571/200000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 4 (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 5 (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 6 (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16519/131072 : ℝ)) 7 (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16519/131072 : ℝ))) (35222892137/200000000000 : ℝ) (176114460691/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35222892137/200000000000 : ℝ) (176114460691/1000000000000 : ℝ) (294028615171/500000000000 : ℝ) (294028615173/500000000000 : ℝ) (104914983643/250000000000 : ℝ) (20982996729/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 1 (294028615171/500000000000 : ℝ) (294028615173/500000000000 : ℝ) (104914983643/250000000000 : ℝ) (20982996729/50000000000 : ℝ) (503858582457/1000000000000 : ℝ) (503858582463/1000000000000 : ℝ) (7762088273/15625000000 : ℝ) (496773649479/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 2 (503858582457/1000000000000 : ℝ) (503858582463/1000000000000 : ℝ) (7762088273/15625000000 : ℝ) (496773649479/1000000000000 : ℝ) (125079028991/250000000000 : ℝ) (500316115971/1000000000000 : ℝ) (500303574667/1000000000000 : ℝ) (250151787337/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 3 (125079028991/250000000000 : ℝ) (500316115971/1000000000000 : ℝ) (500303574667/1000000000000 : ℝ) (250151787337/500000000000 : ℝ) (100061969063/200000000000 : ℝ) (500309845323/1000000000000 : ℝ) (125077461319/250000000000 : ℝ) (125077461321/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 4 (100061969063/200000000000 : ℝ) (500309845323/1000000000000 : ℝ) (125077461319/250000000000 : ℝ) (125077461321/250000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 5 (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 6 (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16519/131072 : ℝ))) 7 (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16519/131072 : ℝ)) hmem 8 (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16519/131072 : ℝ))) hcmem 8 (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16519/131072 : ℝ)) (496084728927/500000000000 : ℝ) (992169457857/1000000000000 : ℝ) (100061969059/200000000000 : ℝ) (62538730663/125000000000 : ℝ) (792087340549/1000000000000 : ℝ) (792087340567/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0292_exp_lower
  have heNumeric : (410980893659/200000000000 : ℝ)/4 ≤ Real.exp (-10657040027197/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980893659/200000000000 : ℝ)/4 ≤ Real.exp ((8259/65536 : ℝ)-(792087340567/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8259/65536 : ℝ) (16519/131072 : ℝ) (792087340567/1000000000000 : ℝ) (410980893659/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0293; no trusted numerical premise.
theorem cover8_leaf0293_exp_radius : (124754075051165781/125000000000000000 : ℝ) ≤ Real.exp ((-2065/131072 : ℝ)/8) ∧ Real.exp ((-2065/131072 : ℝ)/8) ≤ (998032600409326249/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2065/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0293_exp_lower : (920113604354170141/1000000000000000000 : ℝ) ≤ Real.exp ((-21314082193609/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314082193609/32000000000000 : ℝ)/8) ≤ (460056802177085071/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314082193609/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0293_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904330923/1000000000000 : ℝ) ≤ 4*Real.exp (16519/131072 : ℝ)*Real.exp (-mu (radius 8 (2065/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904330923/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2065/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0293_exp_radius
  have hrNumeric : (492184378193/500000000000 : ℝ) ≤ Real.exp (-2065/131072 : ℝ) ∧ Real.exp (-2065/131072 : ℝ) ≤ (984368756387/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492184378193/500000000000 : ℝ) ≤ (radius 8 (2065/16384 : ℝ)) ∧ (radius 8 (2065/16384 : ℝ)) ≤ (984368756387/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2065/16384 : ℝ)) (492184378193/500000000000 : ℝ) (984368756387/1000000000000 : ℝ) (44029926931/250000000000 : ℝ) (176119707731/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2065/16384 : ℝ)) (492184378193/500000000000 : ℝ) (984368756387/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492184378193/500000000000 : ℝ) (984368756387/1000000000000 : ℝ) (992184378193/1000000000000 : ℝ) (496092189097/500000000000 : ℝ) (496076797579/500000000000 : ℝ) (24803839879/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 1 (992184378193/1000000000000 : ℝ) (496092189097/500000000000 : ℝ) (496076797579/500000000000 : ℝ) (24803839879/25000000000 : ℝ) (39686759467/40000000000 : ℝ) (992168986677/1000000000000 : ℝ) (248042246639/250000000000 : ℝ) (496084493279/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 2 (39686759467/40000000000 : ℝ) (992168986677/1000000000000 : ℝ) (248042246639/250000000000 : ℝ) (496084493279/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 3 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 4 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 5 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 6 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2065/16384 : ℝ)) 7 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2065/16384 : ℝ))) (44029926931/250000000000 : ℝ) (176119707731/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44029926931/250000000000 : ℝ) (176119707731/1000000000000 : ℝ) (294029926931/500000000000 : ℝ) (294029926933/500000000000 : ℝ) (209833093031/500000000000 : ℝ) (419666186071/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 1 (294029926931/500000000000 : ℝ) (294029926933/500000000000 : ℝ) (209833093031/500000000000 : ℝ) (419666186071/1000000000000 : ℝ) (251931509981/500000000000 : ℝ) (503863019969/1000000000000 : ℝ) (496778457711/1000000000000 : ℝ) (496778457719/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 2 (251931509981/500000000000 : ℝ) (503863019969/1000000000000 : ℝ) (496778457711/1000000000000 : ℝ) (496778457719/1000000000000 : ℝ) (125080184709/250000000000 : ℝ) (125080184711/250000000000 : ℝ) (500308198967/1000000000000 : ℝ) (7817315609/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 3 (125080184709/250000000000 : ℝ) (125080184711/250000000000 : ℝ) (500308198967/1000000000000 : ℝ) (7817315609/15625000000 : ℝ) (500314468901/1000000000000 : ℝ) (50031446891/100000000000 : ℝ) (250157234431/500000000000 : ℝ) (500314468871/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 4 (500314468901/1000000000000 : ℝ) (50031446891/100000000000 : ℝ) (250157234431/500000000000 : ℝ) (500314468871/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 5 (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 6 (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2065/16384 : ℝ))) 7 (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2065/16384 : ℝ)) hmem 8 (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2065/16384 : ℝ))) hcmem 8 (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2065/16384 : ℝ)) (198433797323/200000000000 : ℝ) (496084493309/500000000000 : ℝ) (500314468881/1000000000000 : ℝ) (500314468891/1000000000000 : ℝ) (792095036793/1000000000000 : ℝ) (198023759203/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0293_exp_lower
  have heNumeric : (2054904330923/1000000000000 : ℝ)/4 ≤ Real.exp (-21314082193609/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904330923/1000000000000 : ℝ)/4 ≤ Real.exp ((16519/131072 : ℝ)-(198023759203/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16519/131072 : ℝ) (2065/16384 : ℝ) (198023759203/250000000000 : ℝ) (2054904330923/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0294; no trusted numerical premise.
theorem cover8_leaf0294_exp_radius : (31188515044830503/31250000000000000 : ℝ) ≤ Real.exp ((-16521/1048576 : ℝ)/8) ∧ Real.exp ((-16521/1048576 : ℝ)/8) ≤ (998032481434576097/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16521/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0294_exp_lower : (920113596700841327/1000000000000000000 : ℝ) ≤ Real.exp ((-2664260540371/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664260540371/4000000000000 : ℝ)/8) ≤ (57507099793802583/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664260540371/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0294_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980838837/200000000000 : ℝ) ≤ 4*Real.exp (2065/16384 : ℝ)*Real.exp (-mu (radius 8 (16521/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980838837/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16521/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0294_exp_radius
  have hrNumeric : (984367817619/1000000000000 : ℝ) ≤ Real.exp (-16521/1048576 : ℝ) ∧ Real.exp (-16521/1048576 : ℝ) ≤ (49218390881/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984367817619/1000000000000 : ℝ) ≤ (radius 8 (16521/131072 : ℝ)) ∧ (radius 8 (16521/131072 : ℝ)) ≤ (49218390881/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16521/131072 : ℝ)) (984367817619/1000000000000 : ℝ) (49218390881/50000000000 : ℝ) (176124954603/1000000000000 : ℝ) (176124954609/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16521/131072 : ℝ)) (984367817619/1000000000000 : ℝ) (49218390881/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984367817619/1000000000000 : ℝ) (49218390881/50000000000 : ℝ) (992183908809/1000000000000 : ℝ) (99218390881/100000000000 : ℝ) (496076561031/500000000000 : ℝ) (62009570129/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 1 (992183908809/1000000000000 : ℝ) (99218390881/100000000000 : ℝ) (496076561031/500000000000 : ℝ) (62009570129/62500000000 : ℝ) (198433703087/200000000000 : ℝ) (992168515437/1000000000000 : ℝ) (248042128829/250000000000 : ℝ) (496084257659/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 2 (198433703087/200000000000 : ℝ) (992168515437/1000000000000 : ℝ) (248042128829/250000000000 : ℝ) (496084257659/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 3 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 4 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 5 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 6 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16521/131072 : ℝ)) 7 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16521/131072 : ℝ))) (176124954603/1000000000000 : ℝ) (176124954609/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176124954603/1000000000000 : ℝ) (176124954609/1000000000000 : ℝ) (588062477301/1000000000000 : ℝ) (117612495461/200000000000 : ℝ) (104918109317/250000000000 : ℝ) (104918109319/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 1 (588062477301/1000000000000 : ℝ) (117612495461/200000000000 : ℝ) (104918109317/250000000000 : ℝ) (104918109319/250000000000 : ℝ) (125966864321/250000000000 : ℝ) (503867457291/1000000000000 : ℝ) (99356653147/200000000000 : ℝ) (248391632871/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 2 (125966864321/250000000000 : ℝ) (503867457291/1000000000000 : ℝ) (99356653147/200000000000 : ℝ) (248391632871/500000000000 : ℝ) (500325361509/1000000000000 : ℝ) (500325361517/1000000000000 : ℝ) (125078205767/250000000000 : ℝ) (125078205769/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 3 (500325361509/1000000000000 : ℝ) (500325361517/1000000000000 : ℝ) (125078205767/250000000000 : ℝ) (125078205769/250000000000 : ℝ) (7817485817/15625000000 : ℝ) (500319092297/1000000000000 : ℝ) (500319092249/1000000000000 : ℝ) (250159546129/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 4 (7817485817/15625000000 : ℝ) (500319092297/1000000000000 : ℝ) (500319092249/1000000000000 : ℝ) (250159546129/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 5 (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 6 (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16521/131072 : ℝ))) 7 (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16521/131072 : ℝ)) hmem 8 (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16521/131072 : ℝ))) hcmem 8 (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16521/131072 : ℝ)) (7937348123/8000000000 : ℝ) (496084257689/500000000000 : ℝ) (125079773067/250000000000 : ℝ) (250159546139/500000000000 : ℝ) (79210273273/100000000000 : ℝ) (792102732749/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0294_exp_lower
  have heNumeric : (410980838837/200000000000 : ℝ)/4 ≤ Real.exp (-2664260540371/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980838837/200000000000 : ℝ)/4 ≤ Real.exp ((2065/16384 : ℝ)-(792102732749/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2065/16384 : ℝ) (16521/131072 : ℝ) (792102732749/1000000000000 : ℝ) (410980838837/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0295; no trusted numerical premise.
theorem cover8_leaf0295_exp_radius : (998032362459840127/1000000000000000000 : ℝ) ≤ Real.exp ((-8261/524288 : ℝ)/8) ∧ Real.exp ((-8261/524288 : ℝ)/8) ≤ (7797127831717501/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-8261/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0295_exp_lower : (460056794541986039/500000000000000000 : ℝ) ≤ Real.exp ((-21314086442183/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314086442183/32000000000000 : ℝ)/8) ≤ (920113589083972079/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314086442183/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0295_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452029049/500000000000 : ℝ) ≤ 4*Real.exp (16521/131072 : ℝ)*Real.exp (-mu (radius 8 (8261/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452029049/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8261/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0295_exp_radius
  have hrNumeric : (984366878853/1000000000000 : ℝ) ≤ Real.exp (-8261/524288 : ℝ) ∧ Real.exp (-8261/524288 : ℝ) ≤ (492183439427/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984366878853/1000000000000 : ℝ) ≤ (radius 8 (8261/65536 : ℝ)) ∧ (radius 8 (8261/65536 : ℝ)) ≤ (492183439427/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8261/65536 : ℝ)) (984366878853/1000000000000 : ℝ) (492183439427/500000000000 : ℝ) (88065100657/500000000000 : ℝ) (176130201321/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8261/65536 : ℝ)) (984366878853/1000000000000 : ℝ) (492183439427/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984366878853/1000000000000 : ℝ) (492183439427/500000000000 : ℝ) (496091719713/500000000000 : ℝ) (992183439427/1000000000000 : ℝ) (992152648967/1000000000000 : ℝ) (124019081121/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 1 (496091719713/500000000000 : ℝ) (992183439427/1000000000000 : ℝ) (992152648967/1000000000000 : ℝ) (124019081121/125000000000 : ℝ) (248042011049/250000000000 : ℝ) (496084022099/500000000000 : ℝ) (992168044077/1000000000000 : ℝ) (992168044079/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 2 (248042011049/250000000000 : ℝ) (496084022099/500000000000 : ℝ) (992168044077/1000000000000 : ℝ) (992168044079/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 3 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 4 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 5 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 6 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8261/65536 : ℝ)) 7 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8261/65536 : ℝ))) (88065100657/500000000000 : ℝ) (176130201321/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88065100657/500000000000 : ℝ) (176130201321/1000000000000 : ℝ) (588065100657/1000000000000 : ℝ) (588065100661/1000000000000 : ℝ) (419678688181/1000000000000 : ℝ) (419678688191/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 1 (588065100657/1000000000000 : ℝ) (588065100661/1000000000000 : ℝ) (419678688181/1000000000000 : ℝ) (419678688191/1000000000000 : ℝ) (503871894419/1000000000000 : ℝ) (251935947213/500000000000 : ℝ) (496788073537/1000000000000 : ℝ) (99357614709/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 2 (503871894419/1000000000000 : ℝ) (251935947213/500000000000 : ℝ) (496788073537/1000000000000 : ℝ) (99357614709/200000000000 : ℝ) (250164991989/500000000000 : ℝ) (250164991993/500000000000 : ℝ) (100063489393/200000000000 : ℝ) (500317446973/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 3 (250164991989/500000000000 : ℝ) (250164991993/500000000000 : ℝ) (100063489393/200000000000 : ℝ) (500317446973/1000000000000 : ℝ) (500323715471/1000000000000 : ℝ) (12508092887/25000000000 : ℝ) (62540464429/125000000000 : ℝ) (500323715441/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 4 (500323715471/1000000000000 : ℝ) (12508092887/25000000000 : ℝ) (62540464429/125000000000 : ℝ) (500323715441/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 5 (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 6 (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8261/65536 : ℝ))) 7 (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8261/65536 : ℝ)) hmem 8 (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8261/65536 : ℝ))) hcmem 8 (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8261/65536 : ℝ)) (124021005517/125000000000 : ℝ) (992168044139/1000000000000 : ℝ) (500323715451/1000000000000 : ℝ) (500323715461/1000000000000 : ℝ) (15842208567/20000000000 : ℝ) (792110428369/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0295_exp_lower
  have heNumeric : (1027452029049/500000000000 : ℝ)/4 ≤ Real.exp (-21314086442183/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452029049/500000000000 : ℝ)/4 ≤ Real.exp ((16521/131072 : ℝ)-(792110428369/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16521/131072 : ℝ) (8261/65536 : ℝ) (792110428369/1000000000000 : ℝ) (1027452029049/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0296; no trusted numerical premise.
theorem cover8_leaf0296_exp_radius : (998032243485118341/1000000000000000000 : ℝ) ≤ Real.exp ((-16523/1048576 : ℝ)/8) ∧ Real.exp ((-16523/1048576 : ℝ)/8) ≤ (499016121742559171/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16523/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0296_exp_lower : (920113581503447379/1000000000000000000 : ℝ) ≤ Real.exp ((-10657044275643/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657044275643/16000000000000 : ℝ)/8) ≤ (46005679075172369/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657044275643/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0296_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745196133/50000000000 : ℝ) ≤ 4*Real.exp (8261/65536 : ℝ)*Real.exp (-mu (radius 8 (16523/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (102745196133/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16523/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0296_exp_radius
  have hrNumeric : (123045742511/125000000000 : ℝ) ≤ Real.exp (-16523/1048576 : ℝ) ∧ Real.exp (-16523/1048576 : ℝ) ≤ (984365940089/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123045742511/125000000000 : ℝ) ≤ (radius 8 (16523/131072 : ℝ)) ∧ (radius 8 (16523/131072 : ℝ)) ≤ (984365940089/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16523/131072 : ℝ)) (123045742511/125000000000 : ℝ) (984365940089/1000000000000 : ℝ) (176135447859/1000000000000 : ℝ) (88067723933/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16523/131072 : ℝ)) (123045742511/125000000000 : ℝ) (984365940089/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123045742511/125000000000 : ℝ) (984365940089/1000000000000 : ℝ) (248045742511/250000000000 : ℝ) (198436594009/200000000000 : ℝ) (3875594437/3906250000 : ℝ) (992152175873/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 1 (248045742511/250000000000 : ℝ) (198436594009/200000000000 : ℝ) (3875594437/3906250000 : ℝ) (992152175873/1000000000000 : ℝ) (496083786479/500000000000 : ℝ) (992167572959/1000000000000 : ℝ) (496083786419/500000000000 : ℝ) (24804189321/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 2 (496083786479/500000000000 : ℝ) (992167572959/1000000000000 : ℝ) (496083786419/500000000000 : ℝ) (24804189321/25000000000 : ℝ) (496083786449/500000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 3 (496083786449/500000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 4 (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 5 (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 6 (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16523/131072 : ℝ)) 7 (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16523/131072 : ℝ))) (176135447859/1000000000000 : ℝ) (88067723933/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176135447859/1000000000000 : ℝ) (88067723933/500000000000 : ℝ) (588067723929/1000000000000 : ℝ) (588067723933/1000000000000 : ℝ) (104921234701/250000000000 : ℝ) (419684938813/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 1 (588067723929/1000000000000 : ℝ) (588067723933/1000000000000 : ℝ) (104921234701/250000000000 : ℝ) (419684938813/1000000000000 : ℝ) (251938165683/500000000000 : ℝ) (503876331373/1000000000000 : ℝ) (248396440559/500000000000 : ℝ) (248396440563/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 2 (251938165683/500000000000 : ℝ) (503876331373/1000000000000 : ℝ) (248396440559/500000000000 : ℝ) (248396440563/500000000000 : ℝ) (250167303121/500000000000 : ℝ) (80053537/160000000 : ℝ) (3908766177/7812500000 : ℝ) (100064414133/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 3 (250167303121/500000000000 : ℝ) (80053537/160000000 : ℝ) (3908766177/7812500000 : ℝ) (100064414133/200000000000 : ℝ) (500328338449/1000000000000 : ℝ) (250164169229/500000000000 : ℝ) (500328338409/1000000000000 : ℝ) (500328338419/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 4 (500328338449/1000000000000 : ℝ) (250164169229/500000000000 : ℝ) (500328338409/1000000000000 : ℝ) (500328338419/1000000000000 : ℝ) (500328338429/1000000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 5 (500328338429/1000000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 6 (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16523/131072 : ℝ))) 7 (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16523/131072 : ℝ)) hmem 8 (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16523/131072 : ℝ))) hcmem 8 (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16523/131072 : ℝ)) (992167572897/1000000000000 : ℝ) (9921675729/10000000000 : ℝ) (125082084607/250000000000 : ℝ) (500328338439/1000000000000 : ℝ) (198029530913/250000000000 : ℝ) (792118123673/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0296_exp_lower
  have heNumeric : (102745196133/50000000000 : ℝ)/4 ≤ Real.exp (-10657044275643/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745196133/50000000000 : ℝ)/4 ≤ Real.exp ((8261/65536 : ℝ)-(792118123673/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8261/65536 : ℝ) (16523/131072 : ℝ) (792118123673/1000000000000 : ℝ) (102745196133/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0297; no trusted numerical premise.
theorem cover8_leaf0297_exp_radius : (499016062255205369/500000000000000000 : ℝ) ≤ Real.exp ((-4131/262144 : ℝ)/8) ∧ Real.exp ((-4131/262144 : ℝ)/8) ≤ (998032124510410739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4131/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0297_exp_lower : (920113573959842299/1000000000000000000 : ℝ) ≤ Real.exp ((-21314090650117/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314090650117/32000000000000 : ℝ)/8) ≤ (9201135739598423/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314090650117/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0297_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451893941/500000000000 : ℝ) ≤ 4*Real.exp (16523/131072 : ℝ)*Real.exp (-mu (radius 8 (4131/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451893941/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4131/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0297_exp_radius
  have hrNumeric : (246091250331/250000000000 : ℝ) ≤ Real.exp (-4131/262144 : ℝ) ∧ Real.exp (-4131/262144 : ℝ) ≤ (39374600053/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246091250331/250000000000 : ℝ) ≤ (radius 8 (4131/32768 : ℝ)) ∧ (radius 8 (4131/32768 : ℝ)) ≤ (39374600053/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4131/32768 : ℝ)) (246091250331/250000000000 : ℝ) (39374600053/40000000000 : ℝ) (176140694237/1000000000000 : ℝ) (176140694243/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4131/32768 : ℝ)) (246091250331/250000000000 : ℝ) (39374600053/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246091250331/250000000000 : ℝ) (39374600053/40000000000 : ℝ) (496091250331/500000000000 : ℝ) (992182500663/1000000000000 : ℝ) (992151702777/1000000000000 : ℝ) (496075851389/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 1 (496091250331/500000000000 : ℝ) (992182500663/1000000000000 : ℝ) (992151702777/1000000000000 : ℝ) (496075851389/500000000000 : ℝ) (992167101719/1000000000000 : ℝ) (992167101721/1000000000000 : ℝ) (1240208877/1250000000 : ℝ) (496083550801/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 2 (992167101719/1000000000000 : ℝ) (992167101721/1000000000000 : ℝ) (1240208877/1250000000 : ℝ) (496083550801/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 3 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 4 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 5 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 6 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4131/32768 : ℝ)) 7 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4131/32768 : ℝ))) (176140694237/1000000000000 : ℝ) (176140694243/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176140694237/1000000000000 : ℝ) (176140694243/1000000000000 : ℝ) (294035173559/500000000000 : ℝ) (294035173561/500000000000 : ℝ) (209845594567/500000000000 : ℝ) (209845594571/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 1 (294035173559/500000000000 : ℝ) (294035173561/500000000000 : ℝ) (209845594567/500000000000 : ℝ) (209845594571/500000000000 : ℝ) (251940384063/500000000000 : ℝ) (125970192033/250000000000 : ℝ) (496797688477/1000000000000 : ℝ) (124199422121/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 2 (251940384063/500000000000 : ℝ) (125970192033/250000000000 : ℝ) (496797688477/1000000000000 : ℝ) (124199422121/250000000000 : ℝ) (500339228301/1000000000000 : ℝ) (125084807077/250000000000 : ℝ) (500326694143/1000000000000 : ℝ) (500326694151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 3 (500339228301/1000000000000 : ℝ) (125084807077/250000000000 : ℝ) (500326694143/1000000000000 : ℝ) (500326694151/1000000000000 : ℝ) (250166480611/500000000000 : ℝ) (50033296123/100000000000 : ℝ) (250166480591/500000000000 : ℝ) (500332961191/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 4 (250166480611/500000000000 : ℝ) (50033296123/100000000000 : ℝ) (250166480591/500000000000 : ℝ) (500332961191/1000000000000 : ℝ) (250166480601/500000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 5 (250166480601/500000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 6 (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4131/32768 : ℝ))) 7 (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4131/32768 : ℝ)) hmem 8 (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4131/32768 : ℝ))) hcmem 8 (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4131/32768 : ℝ)) (992167101659/1000000000000 : ℝ) (496083550831/500000000000 : ℝ) (500332961201/1000000000000 : ℝ) (500332961211/1000000000000 : ℝ) (792125818637/1000000000000 : ℝ) (24753931833/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0297_exp_lower
  have heNumeric : (1027451893941/500000000000 : ℝ)/4 ≤ Real.exp (-21314090650117/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451893941/500000000000 : ℝ)/4 ≤ Real.exp ((16523/131072 : ℝ)-(24753931833/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16523/131072 : ℝ) (4131/32768 : ℝ) (24753931833/31250000000 : ℝ) (1027451893941/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0298; no trusted numerical premise.
theorem cover8_leaf0298_exp_radius : (998032005535717317/1000000000000000000 : ℝ) ≤ Real.exp ((-16525/1048576 : ℝ)/8) ∧ Real.exp ((-16525/1048576 : ℝ)/8) ≤ (499016002767858659/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16525/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0298_exp_lower : (460056783226175869/500000000000000000 : ℝ) ≤ Real.exp ((-213140927389/320000000000 : ℝ)/8) ∧ Real.exp ((-213140927389/320000000000 : ℝ)/8) ≤ (920113566452351739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213140927389/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0298_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1643922923/800000000 : ℝ) ≤ 4*Real.exp (4131/32768 : ℝ)*Real.exp (-mu (radius 8 (16525/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1643922923/800000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16525/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0298_exp_radius
  have hrNumeric : (984364062561/1000000000000 : ℝ) ≤ Real.exp (-16525/1048576 : ℝ) ∧ Real.exp (-16525/1048576 : ℝ) ≤ (492182031281/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984364062561/1000000000000 : ℝ) ≤ (radius 8 (16525/131072 : ℝ)) ∧ (radius 8 (16525/131072 : ℝ)) ≤ (492182031281/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16525/131072 : ℝ)) (984364062561/1000000000000 : ℝ) (492182031281/500000000000 : ℝ) (5504560639/31250000000 : ℝ) (88072970227/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16525/131072 : ℝ)) (984364062561/1000000000000 : ℝ) (492182031281/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984364062561/1000000000000 : ℝ) (492182031281/500000000000 : ℝ) (12402275391/12500000000 : ℝ) (992182031281/1000000000000 : ℝ) (496075614841/500000000000 : ℝ) (248037807421/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 1 (12402275391/12500000000 : ℝ) (992182031281/1000000000000 : ℝ) (496075614841/500000000000 : ℝ) (248037807421/250000000000 : ℝ) (992166630481/1000000000000 : ℝ) (992166630483/1000000000000 : ℝ) (992166630361/1000000000000 : ℝ) (992166630363/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 2 (992166630481/1000000000000 : ℝ) (992166630483/1000000000000 : ℝ) (992166630361/1000000000000 : ℝ) (992166630363/1000000000000 : ℝ) (992166630421/1000000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 3 (992166630421/1000000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 4 (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 5 (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 6 (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16525/131072 : ℝ)) 7 (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16525/131072 : ℝ))) (5504560639/31250000000 : ℝ) (88072970227/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5504560639/31250000000 : ℝ) (88072970227/500000000000 : ℝ) (36754560639/62500000000 : ℝ) (588072970227/1000000000000 : ℝ) (104924359793/250000000000 : ℝ) (20984871959/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 1 (36754560639/62500000000 : ℝ) (588072970227/1000000000000 : ℝ) (104924359793/250000000000 : ℝ) (20984871959/50000000000 : ℝ) (251942602349/500000000000 : ℝ) (15746412647/31250000000 : ℝ) (248401247807/500000000000 : ℝ) (496802495621/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 2 (251942602349/500000000000 : ℝ) (15746412647/31250000000 : ℝ) (248401247807/500000000000 : ℝ) (496802495621/1000000000000 : ℝ) (125085962539/250000000000 : ℝ) (500343850163/1000000000000 : ℝ) (20013252697/40000000000 : ℝ) (500331317433/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 3 (125085962539/250000000000 : ℝ) (500343850163/1000000000000 : ℝ) (20013252697/40000000000 : ℝ) (500331317433/1000000000000 : ℝ) (50033758379/100000000000 : ℝ) (250168791899/500000000000 : ℝ) (500337583751/1000000000000 : ℝ) (500337583759/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 4 (50033758379/100000000000 : ℝ) (250168791899/500000000000 : ℝ) (500337583751/1000000000000 : ℝ) (500337583759/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 5 (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 6 (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16525/131072 : ℝ))) 7 (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16525/131072 : ℝ)) hmem 8 (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16525/131072 : ℝ))) hcmem 8 (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16525/131072 : ℝ)) (49608331521/50000000000 : ℝ) (992166630423/1000000000000 : ℝ) (50033758377/100000000000 : ℝ) (500337583779/1000000000000 : ℝ) (792133513307/1000000000000 : ℝ) (31685340533/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0298_exp_lower
  have heNumeric : (1643922923/800000000 : ℝ)/4 ≤ Real.exp (-213140927389/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1643922923/800000000 : ℝ)/4 ≤ Real.exp ((4131/32768 : ℝ)-(31685340533/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4131/32768 : ℝ) (16525/131072 : ℝ) (31685340533/40000000000 : ℝ) (1643922923/800000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0299; no trusted numerical premise.
theorem cover8_leaf0299_exp_radius : (779712411375811/781250000000000 : ℝ) ≤ Real.exp ((-8263/524288 : ℝ)/8) ∧ Real.exp ((-8263/524288 : ℝ)/8) ≤ (998031886561038081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8263/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0299_exp_lower : (230028389745301431/250000000000000000 : ℝ) ≤ Real.exp ((-21314094817571/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314094817571/32000000000000 : ℝ)/8) ≤ (36804542359248229/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314094817571/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0299_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451760133/500000000000 : ℝ) ≤ 4*Real.exp (16525/131072 : ℝ)*Real.exp (-mu (radius 8 (8263/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451760133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8263/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0299_exp_radius
  have hrNumeric : (984363123799/1000000000000 : ℝ) ≤ Real.exp (-8263/524288 : ℝ) ∧ Real.exp (-8263/524288 : ℝ) ≤ (4921815619/5000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984363123799/1000000000000 : ℝ) ≤ (radius 8 (8263/65536 : ℝ)) ∧ (radius 8 (8263/65536 : ℝ)) ≤ (4921815619/5000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8263/65536 : ℝ)) (984363123799/1000000000000 : ℝ) (4921815619/5000000000 : ℝ) (44037796623/250000000000 : ℝ) (176151186499/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8263/65536 : ℝ)) (984363123799/1000000000000 : ℝ) (4921815619/5000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984363123799/1000000000000 : ℝ) (4921815619/5000000000 : ℝ) (992181561899/1000000000000 : ℝ) (9921815619/10000000000 : ℝ) (248037689147/250000000000 : ℝ) (992150756589/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 1 (992181561899/1000000000000 : ℝ) (9921815619/10000000000 : ℝ) (248037689147/250000000000 : ℝ) (992150756589/1000000000000 : ℝ) (992166159243/1000000000000 : ℝ) (198433231849/200000000000 : ℝ) (992166159123/1000000000000 : ℝ) (7937329273/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 2 (992166159243/1000000000000 : ℝ) (198433231849/200000000000 : ℝ) (992166159123/1000000000000 : ℝ) (7937329273/8000000000 : ℝ) (992166159183/1000000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 3 (992166159183/1000000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 4 (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 5 (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 6 (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8263/65536 : ℝ)) 7 (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8263/65536 : ℝ))) (44037796623/250000000000 : ℝ) (176151186499/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44037796623/250000000000 : ℝ) (176151186499/1000000000000 : ℝ) (294037796623/500000000000 : ℝ) (2352302373/4000000000 : ℝ) (209851844459/500000000000 : ℝ) (13115740279/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 1 (294037796623/500000000000 : ℝ) (2352302373/4000000000 : ℝ) (209851844459/500000000000 : ℝ) (13115740279/31250000000 : ℝ) (251944820541/500000000000 : ℝ) (503889641089/1000000000000 : ℝ) (49680730253/100000000000 : ℝ) (496807302539/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 2 (251944820541/500000000000 : ℝ) (503889641089/1000000000000 : ℝ) (49680730253/100000000000 : ℝ) (496807302539/1000000000000 : ℝ) (250174235903/500000000000 : ℝ) (250174235907/500000000000 : ℝ) (250167970251/500000000000 : ℝ) (500335940511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 3 (250174235903/500000000000 : ℝ) (250174235907/500000000000 : ℝ) (250167970251/500000000000 : ℝ) (500335940511/1000000000000 : ℝ) (250171103077/500000000000 : ℝ) (500342206163/1000000000000 : ℝ) (250171103057/500000000000 : ℝ) (125085551531/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 4 (250171103077/500000000000 : ℝ) (500342206163/1000000000000 : ℝ) (250171103057/500000000000 : ℝ) (125085551531/250000000000 : ℝ) (250171103067/500000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 5 (250171103067/500000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 6 (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8263/65536 : ℝ))) 7 (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8263/65536 : ℝ)) hmem 8 (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8263/65536 : ℝ))) hcmem 8 (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8263/65536 : ℝ)) (496083079591/500000000000 : ℝ) (198433231837/200000000000 : ℝ) (500342206133/1000000000000 : ℝ) (7817846971/15625000000 : ℝ) (792141207657/1000000000000 : ℝ) (396070603839/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0299_exp_lower
  have heNumeric : (1027451760133/500000000000 : ℝ)/4 ≤ Real.exp (-21314094817571/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451760133/500000000000 : ℝ)/4 ≤ Real.exp ((16525/131072 : ℝ)-(396070603839/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16525/131072 : ℝ) (8263/65536 : ℝ) (396070603839/500000000000 : ℝ) (1027451760133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0275_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0275_certificate
#check SmaleRate.Proofs.cover8_leaf0276_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0276_certificate
#check SmaleRate.Proofs.cover8_leaf0277_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0277_certificate
#check SmaleRate.Proofs.cover8_leaf0278_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0278_certificate
#check SmaleRate.Proofs.cover8_leaf0279_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0279_certificate
#check SmaleRate.Proofs.cover8_leaf0280_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0280_certificate
#check SmaleRate.Proofs.cover8_leaf0281_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0281_certificate
#check SmaleRate.Proofs.cover8_leaf0282_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0282_certificate
#check SmaleRate.Proofs.cover8_leaf0283_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0283_certificate
#check SmaleRate.Proofs.cover8_leaf0284_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0284_certificate
#check SmaleRate.Proofs.cover8_leaf0285_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0285_certificate
#check SmaleRate.Proofs.cover8_leaf0286_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0286_certificate
#check SmaleRate.Proofs.cover8_leaf0287_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0287_certificate
#check SmaleRate.Proofs.cover8_leaf0288_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0288_certificate
#check SmaleRate.Proofs.cover8_leaf0289_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0289_certificate
#check SmaleRate.Proofs.cover8_leaf0290_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0290_certificate
#check SmaleRate.Proofs.cover8_leaf0291_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0291_certificate
#check SmaleRate.Proofs.cover8_leaf0292_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0292_certificate
#check SmaleRate.Proofs.cover8_leaf0293_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0293_certificate
#check SmaleRate.Proofs.cover8_leaf0294_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0294_certificate
#check SmaleRate.Proofs.cover8_leaf0295_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0295_certificate
#check SmaleRate.Proofs.cover8_leaf0296_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0296_certificate
#check SmaleRate.Proofs.cover8_leaf0297_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0297_certificate
#check SmaleRate.Proofs.cover8_leaf0298_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0298_certificate
#check SmaleRate.Proofs.cover8_leaf0299_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0299_certificate
