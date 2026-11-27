/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0650; no trusted numerical premise.
theorem cover8_leaf0650_exp_radius : (998013475400345223/1000000000000000000 : ℝ) ≤ Real.exp ((-66723/4194304 : ℝ)/8) ∧ Real.exp ((-66723/4194304 : ℝ)/8) ≤ (124751684425043153/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66723/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0650_exp_lower : (57507093544910847/62500000000000000 : ℝ) ≤ Real.exp ((-341025794251/512000000000 : ℝ)/8) ∧ Real.exp ((-341025794251/512000000000 : ℝ)/8) ≤ (920113496718573553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341025794251/512000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0650_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098048157/20000000000 : ℝ) ≤ 4*Real.exp (33361/262144 : ℝ)*Real.exp (-mu (radius 8 (66723/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (41098048157/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66723/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0650_exp_radius
  have hrNumeric : (7873742889/8000000000 : ℝ) ≤ Real.exp (-66723/4194304 : ℝ) ∧ Real.exp (-66723/4194304 : ℝ) ≤ (492108930563/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7873742889/8000000000 : ℝ) ≤ (radius 8 (66723/524288 : ℝ)) ∧ (radius 8 (66723/524288 : ℝ)) ≤ (492108930563/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66723/524288 : ℝ)) (7873742889/8000000000 : ℝ) (492108930563/500000000000 : ℝ) (35392203571/200000000000 : ℝ) (88480508931/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66723/524288 : ℝ)) (7873742889/8000000000 : ℝ) (492108930563/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7873742889/8000000000 : ℝ) (492108930563/500000000000 : ℝ) (496054465281/500000000000 : ℝ) (992108930563/1000000000000 : ℝ) (992077547939/1000000000000 : ℝ) (49603877397/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 1 (496054465281/500000000000 : ℝ) (992108930563/1000000000000 : ℝ) (992077547939/1000000000000 : ℝ) (49603877397/50000000000 : ℝ) (3968372957/4000000000 : ℝ) (248023309813/250000000000 : ℝ) (496046619563/500000000000 : ℝ) (124011654891/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 2 (3968372957/4000000000 : ℝ) (248023309813/250000000000 : ℝ) (496046619563/500000000000 : ℝ) (124011654891/125000000000 : ℝ) (248023309797/250000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 3 (248023309797/250000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 4 (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 5 (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 6 (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66723/524288 : ℝ)) 7 (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66723/524288 : ℝ))) (35392203571/200000000000 : ℝ) (88480508931/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35392203571/200000000000 : ℝ) (88480508931/500000000000 : ℝ) (588480508927/1000000000000 : ℝ) (588480508931/1000000000000 : ℝ) (84133469643/200000000000 : ℝ) (16826693929/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 1 (588480508927/1000000000000 : ℝ) (588480508931/1000000000000 : ℝ) (84133469643/200000000000 : ℝ) (16826693929/40000000000 : ℝ) (504573928571/1000000000000 : ℝ) (252286964289/500000000000 : ℝ) (497548525439/1000000000000 : ℝ) (497548525447/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 2 (504573928571/1000000000000 : ℝ) (252286964289/500000000000 : ℝ) (497548525439/1000000000000 : ℝ) (497548525447/1000000000000 : ℝ) (100212245401/200000000000 : ℝ) (501061227013/1000000000000 : ℝ) (100209782783/200000000000 : ℝ) (501048913923/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 3 (100212245401/200000000000 : ℝ) (501061227013/1000000000000 : ℝ) (100209782783/200000000000 : ℝ) (501048913923/1000000000000 : ℝ) (25052753523/50000000000 : ℝ) (125263767617/250000000000 : ℝ) (250527535211/500000000000 : ℝ) (501055070431/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 4 (25052753523/50000000000 : ℝ) (125263767617/250000000000 : ℝ) (250527535211/500000000000 : ℝ) (501055070431/1000000000000 : ℝ) (501055070441/1000000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 5 (501055070441/1000000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 6 (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66723/524288 : ℝ))) 7 (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66723/524288 : ℝ)) hmem 8 (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66723/524288 : ℝ))) hcmem 8 (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66723/524288 : ℝ)) (992093239187/1000000000000 : ℝ) (99209323919/100000000000 : ℝ) (12526376761/25000000000 : ℝ) (10021101409/20000000000 : ℝ) (49583007491/62500000000 : ℝ) (6346624959/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0650_exp_lower
  have heNumeric : (41098048157/20000000000 : ℝ)/4 ≤ Real.exp (-341025794251/512000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098048157/20000000000 : ℝ)/4 ≤ Real.exp ((33361/262144 : ℝ)-(6346624959/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33361/262144 : ℝ) (66723/524288 : ℝ) (6346624959/8000000000 : ℝ) (41098048157/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0651; no trusted numerical premise.
theorem cover8_leaf0651_exp_radius : (39920537826289053/40000000000000000 : ℝ) ≤ Real.exp ((-16681/1048576 : ℝ)/8) ∧ Real.exp ((-16681/1048576 : ℝ)/8) ≤ (499006722828613163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16681/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0651_exp_lower : (460056748125729353/500000000000000000 : ℝ) ≤ Real.exp ((-17051289816521/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051289816521/25600000000000 : ℝ)/8) ≤ (920113496251458707/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051289816521/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0651_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431399969/62500000000 : ℝ) ≤ 4*Real.exp (66723/524288 : ℝ)*Real.exp (-mu (radius 8 (16681/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (128431399969/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16681/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0651_exp_radius
  have hrNumeric : (984217626469/1000000000000 : ℝ) ≤ Real.exp (-16681/1048576 : ℝ) ∧ Real.exp (-16681/1048576 : ℝ) ≤ (98421762647/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984217626469/1000000000000 : ℝ) ≤ (radius 8 (16681/131072 : ℝ)) ∧ (radius 8 (16681/131072 : ℝ)) ≤ (98421762647/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16681/131072 : ℝ)) (984217626469/1000000000000 : ℝ) (98421762647/100000000000 : ℝ) (35392464591/200000000000 : ℝ) (176962322961/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16681/131072 : ℝ)) (984217626469/1000000000000 : ℝ) (98421762647/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984217626469/1000000000000 : ℝ) (98421762647/100000000000 : ℝ) (496054406617/500000000000 : ℝ) (198421762647/200000000000 : ℝ) (496038714837/500000000000 : ℝ) (39683097187/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 1 (496054406617/500000000000 : ℝ) (198421762647/200000000000 : ℝ) (496038714837/500000000000 : ℝ) (39683097187/40000000000 : ℝ) (496046560727/500000000000 : ℝ) (198418624291/200000000000 : ℝ) (992093121329/1000000000000 : ℝ) (992093121331/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 2 (496046560727/500000000000 : ℝ) (198418624291/200000000000 : ℝ) (992093121329/1000000000000 : ℝ) (992093121331/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 3 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 4 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 5 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 6 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16681/131072 : ℝ)) 7 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16681/131072 : ℝ))) (35392464591/200000000000 : ℝ) (176962322961/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35392464591/200000000000 : ℝ) (176962322961/1000000000000 : ℝ) (588481161477/1000000000000 : ℝ) (588481161481/1000000000000 : ℝ) (210334449719/500000000000 : ℝ) (210334449723/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 1 (588481161477/1000000000000 : ℝ) (588481161481/1000000000000 : ℝ) (210334449719/500000000000 : ℝ) (210334449723/500000000000 : ℝ) (504575030457/1000000000000 : ℝ) (7883984851/15625000000 : ℝ) (497549718659/1000000000000 : ℝ) (497549718667/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 2 (504575030457/1000000000000 : ℝ) (7883984851/15625000000 : ℝ) (497549718659/1000000000000 : ℝ) (497549718667/1000000000000 : ℝ) (250531187279/500000000000 : ℝ) (250531187283/500000000000 : ℝ) (62631257727/125000000000 : ℝ) (489306701/976562500 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 3 (250531187279/500000000000 : ℝ) (250531187283/500000000000 : ℝ) (62631257727/125000000000 : ℝ) (489306701/976562500 : ℝ) (501056218187/1000000000000 : ℝ) (100211243639/200000000000 : ℝ) (501056218149/1000000000000 : ℝ) (250528109079/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 4 (501056218187/1000000000000 : ℝ) (100211243639/200000000000 : ℝ) (501056218149/1000000000000 : ℝ) (250528109079/500000000000 : ℝ) (62632027271/125000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 5 (62632027271/125000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 6 (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16681/131072 : ℝ))) 7 (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16681/131072 : ℝ)) hmem 8 (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16681/131072 : ℝ))) hcmem 8 (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16681/131072 : ℝ)) (992093121391/1000000000000 : ℝ) (992093121393/1000000000000 : ℝ) (501056218167/1000000000000 : ℝ) (501056218177/1000000000000 : ℝ) (396665015633/500000000000 : ℝ) (158666006257/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0651_exp_lower
  have heNumeric : (128431399969/62500000000 : ℝ)/4 ≤ Real.exp (-17051289816521/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431399969/62500000000 : ℝ)/4 ≤ Real.exp ((66723/524288 : ℝ)-(158666006257/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66723/524288 : ℝ) (16681/131072 : ℝ) (158666006257/200000000000 : ℝ) (128431399969/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0652; no trusted numerical premise.
theorem cover8_leaf0652_exp_radius : (499006707957054157/500000000000000000 : ℝ) ≤ Real.exp ((-66725/4194304 : ℝ)/8) ∧ Real.exp ((-66725/4194304 : ℝ)/8) ≤ (199602683182821663/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66725/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0652_exp_lower : (920113495786414117/1000000000000000000 : ℝ) ≤ Real.exp ((-21314112400039/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314112400039/32000000000000 : ℝ)/8) ≤ (460056747893207059/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314112400039/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0652_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725597799/250000000000 : ℝ) ≤ 4*Real.exp (16681/131072 : ℝ)*Real.exp (-mu (radius 8 (66725/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725597799/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66725/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0652_exp_radius
  have hrNumeric : (984217391813/1000000000000 : ℝ) ≤ Real.exp (-66725/4194304 : ℝ) ∧ Real.exp (-66725/4194304 : ℝ) ≤ (492108695907/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984217391813/1000000000000 : ℝ) ≤ (radius 8 (66725/524288 : ℝ)) ∧ (radius 8 (66725/524288 : ℝ)) ≤ (492108695907/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66725/524288 : ℝ)) (984217391813/1000000000000 : ℝ) (492108695907/500000000000 : ℝ) (44240907011/250000000000 : ℝ) (176963628051/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66725/524288 : ℝ)) (984217391813/1000000000000 : ℝ) (492108695907/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984217391813/1000000000000 : ℝ) (492108695907/500000000000 : ℝ) (496054347953/500000000000 : ℝ) (992108695907/1000000000000 : ℝ) (992077311409/1000000000000 : ℝ) (99207731141/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 1 (496054347953/500000000000 : ℝ) (992108695907/1000000000000 : ℝ) (992077311409/1000000000000 : ℝ) (99207731141/100000000000 : ℝ) (992093003657/1000000000000 : ℝ) (992093003659/1000000000000 : ℝ) (992093003533/1000000000000 : ℝ) (198418600707/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 2 (992093003657/1000000000000 : ℝ) (992093003659/1000000000000 : ℝ) (992093003533/1000000000000 : ℝ) (198418600707/200000000000 : ℝ) (198418600719/200000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 3 (198418600719/200000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 4 (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 5 (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 6 (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66725/524288 : ℝ)) 7 (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66725/524288 : ℝ))) (44240907011/250000000000 : ℝ) (176963628051/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44240907011/250000000000 : ℝ) (176963628051/1000000000000 : ℝ) (294240907011/500000000000 : ℝ) (294240907013/500000000000 : ℝ) (210335225321/500000000000 : ℝ) (105167612663/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 1 (294240907011/500000000000 : ℝ) (294240907013/500000000000 : ℝ) (210335225321/500000000000 : ℝ) (105167612663/250000000000 : ℝ) (126144033083/250000000000 : ℝ) (504576132339/1000000000000 : ℝ) (248775455933/500000000000 : ℝ) (796081459/1600000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 2 (126144033083/250000000000 : ℝ) (504576132339/1000000000000 : ℝ) (248775455933/500000000000 : ℝ) (796081459/1600000000 : ℝ) (501063522099/1000000000000 : ℝ) (501063522107/1000000000000 : ℝ) (100210241941/200000000000 : ℝ) (250525604857/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 3 (501063522099/1000000000000 : ℝ) (501063522107/1000000000000 : ℝ) (100210241941/200000000000 : ℝ) (250525604857/500000000000 : ℝ) (250528682951/500000000000 : ℝ) (501057365911/1000000000000 : ℝ) (62632170733/125000000000 : ℝ) (501057365873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 4 (250528682951/500000000000 : ℝ) (501057365911/1000000000000 : ℝ) (62632170733/125000000000 : ℝ) (501057365873/1000000000000 : ℝ) (501057365883/1000000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 5 (501057365883/1000000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 6 (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66725/524288 : ℝ))) 7 (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66725/524288 : ℝ)) hmem 8 (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66725/524288 : ℝ))) hcmem 8 (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66725/524288 : ℝ)) (496046501797/500000000000 : ℝ) (992093003597/1000000000000 : ℝ) (250528682941/500000000000 : ℝ) (125264341473/250000000000 : ℝ) (793331942657/1000000000000 : ℝ) (793331942677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0652_exp_lower
  have heNumeric : (513725597799/250000000000 : ℝ)/4 ≤ Real.exp (-21314112400039/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725597799/250000000000 : ℝ)/4 ≤ Real.exp ((16681/131072 : ℝ)-(793331942677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16681/131072 : ℝ) (66725/524288 : ℝ) (793331942677/1000000000000 : ℝ) (513725597799/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0653; no trusted numerical premise.
theorem cover8_leaf0653_exp_radius : (998013386170991189/1000000000000000000 : ℝ) ≤ Real.exp ((-33363/2097152 : ℝ)/8) ∧ Real.exp ((-33363/2097152 : ℝ)/8) ≤ (99801338617099119/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33363/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0653_exp_lower : (230028373831147481/250000000000000000 : ℝ) ≤ Real.exp ((-85256450114123/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256450114123/128000000000000 : ℝ)/8) ≤ (36804539812983597/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256450114123/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0653_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215699467/31250000000 : ℝ) ≤ 4*Real.exp (66725/524288 : ℝ)*Real.exp (-mu (radius 8 (33363/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (64215699467/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33363/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0653_exp_radius
  have hrNumeric : (492108578579/500000000000 : ℝ) ≤ Real.exp (-33363/2097152 : ℝ) ∧ Real.exp (-33363/2097152 : ℝ) ≤ (984217157159/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492108578579/500000000000 : ℝ) ≤ (radius 8 (33363/262144 : ℝ)) ∧ (radius 8 (33363/262144 : ℝ)) ≤ (984217157159/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33363/262144 : ℝ)) (492108578579/500000000000 : ℝ) (984217157159/1000000000000 : ℝ) (176964933119/1000000000000 : ℝ) (283143893/1600000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33363/262144 : ℝ)) (492108578579/500000000000 : ℝ) (984217157159/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492108578579/500000000000 : ℝ) (984217157159/1000000000000 : ℝ) (992108578579/1000000000000 : ℝ) (49605428929/50000000000 : ℝ) (124009649143/125000000000 : ℝ) (496038596573/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 1 (992108578579/1000000000000 : ℝ) (49605428929/50000000000 : ℝ) (124009649143/125000000000 : ℝ) (496038596573/500000000000 : ℝ) (992092885861/1000000000000 : ℝ) (992092885863/1000000000000 : ℝ) (992092885737/1000000000000 : ℝ) (992092885739/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 2 (992092885861/1000000000000 : ℝ) (992092885863/1000000000000 : ℝ) (992092885737/1000000000000 : ℝ) (992092885739/1000000000000 : ℝ) (992092885799/1000000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 3 (992092885799/1000000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 4 (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 5 (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 6 (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33363/262144 : ℝ)) 7 (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33363/262144 : ℝ))) (176964933119/1000000000000 : ℝ) (283143893/1600000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176964933119/1000000000000 : ℝ) (283143893/1600000000 : ℝ) (588482466559/1000000000000 : ℝ) (588482466563/1000000000000 : ℝ) (13146000057/31250000000 : ℝ) (52584000229/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 1 (588482466559/1000000000000 : ℝ) (588482466563/1000000000000 : ℝ) (13146000057/31250000000 : ℝ) (52584000229/125000000000 : ℝ) (504577234191/1000000000000 : ℝ) (252288617099/500000000000 : ℝ) (15548503283/31250000000 : ℝ) (497552105063/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 2 (504577234191/1000000000000 : ℝ) (252288617099/500000000000 : ℝ) (15548503283/31250000000 : ℝ) (497552105063/1000000000000 : ℝ) (501064669623/1000000000000 : ℝ) (501064669631/1000000000000 : ℝ) (250526178789/500000000000 : ℝ) (250526178793/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 3 (501064669623/1000000000000 : ℝ) (501064669631/1000000000000 : ℝ) (250526178789/500000000000 : ℝ) (250526178793/500000000000 : ℝ) (313161571/625000000 : ℝ) (501058513609/1000000000000 : ℝ) (250529256781/500000000000 : ℝ) (501058513571/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 4 (313161571/625000000 : ℝ) (501058513609/1000000000000 : ℝ) (250529256781/500000000000 : ℝ) (501058513571/1000000000000 : ℝ) (501058513581/1000000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 5 (501058513581/1000000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 6 (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33363/262144 : ℝ))) 7 (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33363/262144 : ℝ)) hmem 8 (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33363/262144 : ℝ))) hcmem 8 (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33363/262144 : ℝ)) (496046442899/500000000000 : ℝ) (992092885801/1000000000000 : ℝ) (25052925679/50000000000 : ℝ) (50105851359/100000000000 : ℝ) (396666927011/500000000000 : ℝ) (793333854041/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0653_exp_lower
  have heNumeric : (64215699467/31250000000 : ℝ)/4 ≤ Real.exp (-85256450114123/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215699467/31250000000 : ℝ)/4 ≤ Real.exp ((66725/524288 : ℝ)-(793333854041/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66725/524288 : ℝ) (33363/262144 : ℝ) (793333854041/1000000000000 : ℝ) (64215699467/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0654; no trusted numerical premise.
theorem cover8_leaf0654_exp_radius : (19960267128557499/20000000000000000 : ℝ) ≤ Real.exp ((-66727/4194304 : ℝ)/8) ∧ Real.exp ((-66727/4194304 : ℝ)/8) ≤ (998013356427874951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66727/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0654_exp_lower : (460056747431957937/500000000000000000 : ℝ) ≤ Real.exp ((-8525645062681/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525645062681/12800000000000 : ℝ)/8) ≤ (7360907958911327/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525645062681/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0654_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451187357/500000000000 : ℝ) ≤ 4*Real.exp (33363/262144 : ℝ)*Real.exp (-mu (radius 8 (66727/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451187357/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66727/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0654_exp_radius
  have hrNumeric : (492108461251/500000000000 : ℝ) ≤ Real.exp (-66727/4194304 : ℝ) ∧ Real.exp (-66727/4194304 : ℝ) ≤ (984216922503/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492108461251/500000000000 : ℝ) ≤ (radius 8 (66727/524288 : ℝ)) ∧ (radius 8 (66727/524288 : ℝ)) ≤ (984216922503/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66727/524288 : ℝ)) (492108461251/500000000000 : ℝ) (984216922503/1000000000000 : ℝ) (44241559547/250000000000 : ℝ) (35393247639/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66727/524288 : ℝ)) (492108461251/500000000000 : ℝ) (984216922503/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492108461251/500000000000 : ℝ) (984216922503/1000000000000 : ℝ) (992108461251/1000000000000 : ℝ) (248027115313/250000000000 : ℝ) (992077074879/1000000000000 : ℝ) (992077074881/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 1 (992108461251/1000000000000 : ℝ) (248027115313/250000000000 : ℝ) (992077074879/1000000000000 : ℝ) (992077074881/1000000000000 : ℝ) (198418553613/200000000000 : ℝ) (992092768067/1000000000000 : ℝ) (49604638397/50000000000 : ℝ) (992092767943/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 2 (198418553613/200000000000 : ℝ) (992092768067/1000000000000 : ℝ) (49604638397/50000000000 : ℝ) (992092767943/1000000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 3 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 4 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 5 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 6 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66727/524288 : ℝ)) 7 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66727/524288 : ℝ))) (44241559547/250000000000 : ℝ) (35393247639/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44241559547/250000000000 : ℝ) (35393247639/200000000000 : ℝ) (294241559547/500000000000 : ℝ) (294241559549/500000000000 : ℝ) (420673552993/1000000000000 : ℝ) (210336776501/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 1 (294241559547/500000000000 : ℝ) (294241559549/500000000000 : ℝ) (420673552993/1000000000000 : ℝ) (210336776501/500000000000 : ℝ) (504578336043/1000000000000 : ℝ) (10091566721/20000000000 : ℝ) (124388324559/250000000000 : ℝ) (124388324561/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 2 (504578336043/1000000000000 : ℝ) (10091566721/20000000000 : ℝ) (124388324559/250000000000 : ℝ) (124388324561/250000000000 : ℝ) (501065817139/1000000000000 : ℝ) (501065817147/1000000000000 : ℝ) (250526752721/500000000000 : ℝ) (501053505451/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 3 (501065817139/1000000000000 : ℝ) (501065817147/1000000000000 : ℝ) (250526752721/500000000000 : ℝ) (501053505451/1000000000000 : ℝ) (50105966129/100000000000 : ℝ) (501059661299/1000000000000 : ℝ) (125264915313/250000000000 : ℝ) (250529830631/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 4 (50105966129/100000000000 : ℝ) (501059661299/1000000000000 : ℝ) (125264915313/250000000000 : ℝ) (250529830631/500000000000 : ℝ) (501059661271/1000000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 5 (501059661271/1000000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 6 (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66727/524288 : ℝ))) 7 (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66727/524288 : ℝ)) hmem 8 (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66727/524288 : ℝ))) hcmem 8 (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66727/524288 : ℝ)) (496046384001/500000000000 : ℝ) (198418553601/200000000000 : ℝ) (50105966127/100000000000 : ℝ) (501059661281/1000000000000 : ℝ) (396667882687/500000000000 : ℝ) (158667153079/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0654_exp_lower
  have heNumeric : (1027451187357/500000000000 : ℝ)/4 ≤ Real.exp (-8525645062681/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451187357/500000000000 : ℝ)/4 ≤ Real.exp ((33363/262144 : ℝ)-(158667153079/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33363/262144 : ℝ) (66727/524288 : ℝ) (158667153079/200000000000 : ℝ) (1027451187357/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0655; no trusted numerical premise.
theorem cover8_leaf0655_exp_radius : (499006663342379799/500000000000000000 : ℝ) ≤ Real.exp ((-8341/524288 : ℝ)/8) ∧ Real.exp ((-8341/524288 : ℝ)/8) ≤ (998013326684759599/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8341/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0655_exp_lower : (920113494405312079/1000000000000000000 : ℝ) ≤ Real.exp ((-85256451137193/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256451137193/128000000000000 : ℝ)/8) ≤ (11501418680066401/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256451137193/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0655_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372559163/25000000000 : ℝ) ≤ 4*Real.exp (66727/524288 : ℝ)*Real.exp (-mu (radius 8 (8341/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (51372559163/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8341/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0655_exp_radius
  have hrNumeric : (492108343923/500000000000 : ℝ) ≤ Real.exp (-8341/524288 : ℝ) ∧ Real.exp (-8341/524288 : ℝ) ≤ (984216687847/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492108343923/500000000000 : ℝ) ≤ (radius 8 (8341/65536 : ℝ)) ∧ (radius 8 (8341/65536 : ℝ)) ≤ (984216687847/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8341/65536 : ℝ)) (492108343923/500000000000 : ℝ) (984216687847/1000000000000 : ℝ) (11060471453/62500000000 : ℝ) (35393508651/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8341/65536 : ℝ)) (492108343923/500000000000 : ℝ) (984216687847/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492108343923/500000000000 : ℝ) (984216687847/1000000000000 : ℝ) (992108343923/1000000000000 : ℝ) (248027085981/250000000000 : ℝ) (496038478307/500000000000 : ℝ) (124009619577/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 1 (992108343923/1000000000000 : ℝ) (248027085981/250000000000 : ℝ) (496038478307/500000000000 : ℝ) (124009619577/125000000000 : ℝ) (248023162567/250000000000 : ℝ) (99209265027/100000000000 : ℝ) (31002895317/31250000000 : ℝ) (496046325073/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 2 (248023162567/250000000000 : ℝ) (99209265027/100000000000 : ℝ) (31002895317/31250000000 : ℝ) (496046325073/500000000000 : ℝ) (496046325103/500000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 3 (496046325103/500000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 4 (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 5 (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 6 (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8341/65536 : ℝ)) 7 (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8341/65536 : ℝ))) (11060471453/62500000000 : ℝ) (35393508651/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11060471453/62500000000 : ℝ) (35393508651/200000000000 : ℝ) (73560471453/125000000000 : ℝ) (147120942907/250000000000 : ℝ) (84135020829/200000000000 : ℝ) (84135020831/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 1 (73560471453/125000000000 : ℝ) (147120942907/250000000000 : ℝ) (84135020829/200000000000 : ℝ) (84135020831/200000000000 : ℝ) (126144859471/250000000000 : ℝ) (126144859473/250000000000 : ℝ) (497554491403/1000000000000 : ℝ) (497554491411/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 2 (126144859471/250000000000 : ℝ) (126144859473/250000000000 : ℝ) (497554491403/1000000000000 : ℝ) (497554491411/1000000000000 : ℝ) (501066964643/1000000000000 : ℝ) (125266741163/250000000000 : ℝ) (100210930659/200000000000 : ℝ) (62631831663/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 3 (501066964643/1000000000000 : ℝ) (125266741163/250000000000 : ℝ) (100210930659/200000000000 : ℝ) (62631831663/125000000000 : ℝ) (501060808969/1000000000000 : ℝ) (250530404489/500000000000 : ℝ) (501060808931/1000000000000 : ℝ) (501060808941/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 4 (501060808969/1000000000000 : ℝ) (250530404489/500000000000 : ℝ) (501060808931/1000000000000 : ℝ) (501060808941/1000000000000 : ℝ) (10021216179/20000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 5 (10021216179/20000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 6 (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8341/65536 : ℝ))) 7 (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8341/65536 : ℝ)) hmem 8 (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8341/65536 : ℝ))) hcmem 8 (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8341/65536 : ℝ)) (198418530041/200000000000 : ℝ) (31002895319/31250000000 : ℝ) (501060808949/1000000000000 : ℝ) (391453757/781250000 : ℝ) (79333767671/100000000000 : ℝ) (793337676731/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0655_exp_lower
  have heNumeric : (51372559163/25000000000 : ℝ)/4 ≤ Real.exp (-85256451137193/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372559163/25000000000 : ℝ)/4 ≤ Real.exp ((66727/524288 : ℝ)-(793337676731/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66727/524288 : ℝ) (8341/65536 : ℝ) (793337676731/1000000000000 : ℝ) (51372559163/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0656; no trusted numerical premise.
theorem cover8_leaf0656_exp_radius : (249503324235411283/250000000000000000 : ℝ) ≤ Real.exp ((-66729/4194304 : ℝ)/8) ∧ Real.exp ((-66729/4194304 : ℝ)/8) ≤ (998013296941645133/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66729/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0656_exp_lower : (920113493950158711/1000000000000000000 : ℝ) ≤ Real.exp ((-10657056455467/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657056455467/16000000000000 : ℝ)/8) ≤ (115014186743769839/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657056455467/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0656_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725589597/250000000000 : ℝ) ≤ 4*Real.exp (8341/65536 : ℝ)*Real.exp (-mu (radius 8 (66729/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725589597/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66729/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0656_exp_radius
  have hrNumeric : (984216453191/1000000000000 : ℝ) ≤ Real.exp (-66729/4194304 : ℝ) ∧ Real.exp (-66729/4194304 : ℝ) ≤ (123027056649/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984216453191/1000000000000 : ℝ) ≤ (radius 8 (66729/524288 : ℝ)) ∧ (radius 8 (66729/524288 : ℝ)) ≤ (123027056649/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66729/524288 : ℝ)) (984216453191/1000000000000 : ℝ) (123027056649/125000000000 : ℝ) (176968848293/1000000000000 : ℝ) (176968848299/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66729/524288 : ℝ)) (984216453191/1000000000000 : ℝ) (123027056649/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984216453191/1000000000000 : ℝ) (123027056649/125000000000 : ℝ) (198421645319/200000000000 : ℝ) (248027056649/250000000000 : ℝ) (19841536767/20000000000 : ℝ) (992076838351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 1 (198421645319/200000000000 : ℝ) (248027056649/250000000000 : ℝ) (19841536767/20000000000 : ℝ) (992076838351/1000000000000 : ℝ) (124011566559/125000000000 : ℝ) (496046266237/500000000000 : ℝ) (248023133087/250000000000 : ℝ) (19841850647/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 2 (124011566559/125000000000 : ℝ) (496046266237/500000000000 : ℝ) (248023133087/250000000000 : ℝ) (19841850647/20000000000 : ℝ) (99209253241/100000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 3 (99209253241/100000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 4 (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 5 (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 6 (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66729/524288 : ℝ)) 7 (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66729/524288 : ℝ))) (176968848293/1000000000000 : ℝ) (176968848299/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176968848293/1000000000000 : ℝ) (176968848299/1000000000000 : ℝ) (294242212073/500000000000 : ℝ) (11769688483/20000000000 : ℝ) (210338327637/500000000000 : ℝ) (210338327641/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 1 (294242212073/500000000000 : ℝ) (11769688483/20000000000 : ℝ) (210338327637/500000000000 : ℝ) (210338327641/500000000000 : ℝ) (50458053971/100000000000 : ℝ) (126145134929/250000000000 : ℝ) (62194460569/125000000000 : ℝ) (6219446057/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 2 (50458053971/100000000000 : ℝ) (126145134929/250000000000 : ℝ) (62194460569/125000000000 : ℝ) (6219446057/12500000000 : ℝ) (501068112131/1000000000000 : ℝ) (250534056069/500000000000 : ℝ) (50105580113/100000000000 : ℝ) (501055801139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 3 (501068112131/1000000000000 : ℝ) (250534056069/500000000000 : ℝ) (50105580113/100000000000 : ℝ) (501055801139/1000000000000 : ℝ) (50106195663/100000000000 : ℝ) (501061956639/1000000000000 : ℝ) (31316372287/62500000000 : ℝ) (501061956601/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 4 (50106195663/100000000000 : ℝ) (501061956639/1000000000000 : ℝ) (31316372287/62500000000 : ℝ) (501061956601/1000000000000 : ℝ) (501061956611/1000000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 5 (501061956611/1000000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 6 (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66729/524288 : ℝ))) 7 (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66729/524288 : ℝ)) hmem 8 (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66729/524288 : ℝ))) hcmem 8 (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66729/524288 : ℝ)) (992092532409/1000000000000 : ℝ) (248023133103/250000000000 : ℝ) (50106195661/100000000000 : ℝ) (25053097831/50000000000 : ℝ) (396669794009/500000000000 : ℝ) (793339588037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0656_exp_lower
  have heNumeric : (513725589597/250000000000 : ℝ)/4 ≤ Real.exp (-10657056455467/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725589597/250000000000 : ℝ)/4 ≤ Real.exp ((8341/65536 : ℝ)-(793339588037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8341/65536 : ℝ) (66729/524288 : ℝ) (793339588037/1000000000000 : ℝ) (513725589597/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0657; no trusted numerical premise.
theorem cover8_leaf0657_exp_radius : (998013267198531553/1000000000000000000 : ℝ) ≤ Real.exp ((-33365/2097152 : ℝ)/8) ∧ Real.exp ((-33365/2097152 : ℝ)/8) ≤ (499006633599265777/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33365/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0657_exp_lower : (92011349349604047/100000000000000000 : ℝ) ≤ Real.exp ((-85256452149127/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256452149127/128000000000000 : ℝ)/8) ≤ (920113493496040471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256452149127/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0657_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196094011/40000000000 : ℝ) ≤ 4*Real.exp (66729/524288 : ℝ)*Real.exp (-mu (radius 8 (33365/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (82196094011/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33365/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0657_exp_radius
  have hrNumeric : (196843243707/200000000000 : ℝ) ≤ Real.exp (-33365/2097152 : ℝ) ∧ Real.exp (-33365/2097152 : ℝ) ≤ (123027027317/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196843243707/200000000000 : ℝ) ≤ (radius 8 (33365/262144 : ℝ)) ∧ (radius 8 (33365/262144 : ℝ)) ≤ (123027027317/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33365/262144 : ℝ)) (196843243707/200000000000 : ℝ) (123027027317/125000000000 : ℝ) (44242538333/250000000000 : ℝ) (176970153339/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33365/262144 : ℝ)) (196843243707/200000000000 : ℝ) (123027027317/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196843243707/200000000000 : ℝ) (123027027317/125000000000 : ℝ) (992108109267/1000000000000 : ℝ) (248027027317/250000000000 : ℝ) (198415344017/200000000000 : ℝ) (496038360043/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 1 (992108109267/1000000000000 : ℝ) (248027027317/250000000000 : ℝ) (198415344017/200000000000 : ℝ) (496038360043/500000000000 : ℝ) (248023103669/250000000000 : ℝ) (992092414677/1000000000000 : ℝ) (992092414551/1000000000000 : ℝ) (992092414553/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 2 (248023103669/250000000000 : ℝ) (992092414677/1000000000000 : ℝ) (992092414551/1000000000000 : ℝ) (992092414553/1000000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 3 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 4 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 5 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 6 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33365/262144 : ℝ)) 7 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33365/262144 : ℝ))) (44242538333/250000000000 : ℝ) (176970153339/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44242538333/250000000000 : ℝ) (176970153339/1000000000000 : ℝ) (294242538333/500000000000 : ℝ) (58848507667/100000000000 : ℝ) (42067820639/100000000000 : ℝ) (420678206399/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 1 (294242538333/500000000000 : ℝ) (58848507667/100000000000 : ℝ) (42067820639/100000000000 : ℝ) (420678206399/1000000000000 : ℝ) (63072705191/125000000000 : ℝ) (100916328307/200000000000 : ℝ) (124389219423/250000000000 : ℝ) (4975568777/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 2 (63072705191/125000000000 : ℝ) (100916328307/200000000000 : ℝ) (124389219423/250000000000 : ℝ) (4975568777/10000000000 : ℝ) (50106925961/100000000000 : ℝ) (250534629809/500000000000 : ℝ) (250528474479/500000000000 : ℝ) (250528474483/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 3 (50106925961/100000000000 : ℝ) (250534629809/500000000000 : ℝ) (250528474479/500000000000 : ℝ) (250528474483/500000000000 : ℝ) (125265776071/250000000000 : ℝ) (125265776073/250000000000 : ℝ) (250531552123/500000000000 : ℝ) (100212620851/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 4 (125265776071/250000000000 : ℝ) (125265776073/250000000000 : ℝ) (250531552123/500000000000 : ℝ) (100212620851/200000000000 : ℝ) (100212620853/200000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 5 (100212620853/200000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 6 (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33365/262144 : ℝ))) 7 (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33365/262144 : ℝ)) hmem 8 (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33365/262144 : ℝ))) hcmem 8 (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33365/262144 : ℝ)) (992092414613/1000000000000 : ℝ) (198418482923/200000000000 : ℝ) (62632888033/125000000000 : ℝ) (250531552137/500000000000 : ℝ) (158668299863/200000000000 : ℝ) (396670749667/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0657_exp_lower
  have heNumeric : (82196094011/40000000000 : ℝ)/4 ≤ Real.exp (-85256452149127/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196094011/40000000000 : ℝ)/4 ≤ Real.exp ((66729/524288 : ℝ)-(396670749667/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66729/524288 : ℝ) (33365/262144 : ℝ) (396670749667/500000000000 : ℝ) (82196094011/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0658; no trusted numerical premise.
theorem cover8_leaf0658_exp_radius : (998013237455418859/1000000000000000000 : ℝ) ≤ Real.exp ((-66731/4194304 : ℝ)/8) ∧ Real.exp ((-66731/4194304 : ℝ)/8) ≤ (49900661872770943/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66731/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0658_exp_lower : (23002837326131441/25000000000000000 : ℝ) ≤ Real.exp ((-42628226325403/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628226325403/64000000000000 : ℝ)/8) ≤ (920113493045257641/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628226325403/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0658_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902342221/1000000000000 : ℝ) ≤ 4*Real.exp (33365/262144 : ℝ)*Real.exp (-mu (radius 8 (66731/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902342221/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66731/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0658_exp_radius
  have hrNumeric : (24605399597/25000000000 : ℝ) ≤ Real.exp (-66731/4194304 : ℝ) ∧ Real.exp (-66731/4194304 : ℝ) ≤ (984215983881/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24605399597/25000000000 : ℝ) ≤ (radius 8 (66731/524288 : ℝ)) ∧ (radius 8 (66731/524288 : ℝ)) ≤ (984215983881/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66731/524288 : ℝ)) (24605399597/25000000000 : ℝ) (984215983881/1000000000000 : ℝ) (176971458357/1000000000000 : ℝ) (176971458363/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66731/524288 : ℝ)) (24605399597/25000000000 : ℝ) (984215983881/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24605399597/25000000000 : ℝ) (984215983881/1000000000000 : ℝ) (49605399597/50000000000 : ℝ) (992107991941/1000000000000 : ℝ) (49603830091/50000000000 : ℝ) (496038300911/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 1 (49605399597/50000000000 : ℝ) (992107991941/1000000000000 : ℝ) (49603830091/50000000000 : ℝ) (496038300911/500000000000 : ℝ) (12401153711/12500000000 : ℝ) (496046148441/500000000000 : ℝ) (198418459351/200000000000 : ℝ) (496046148379/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 2 (12401153711/12500000000 : ℝ) (496046148441/500000000000 : ℝ) (198418459351/200000000000 : ℝ) (496046148379/500000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 3 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 4 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 5 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 6 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66731/524288 : ℝ)) 7 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66731/524288 : ℝ))) (176971458357/1000000000000 : ℝ) (176971458363/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176971458357/1000000000000 : ℝ) (176971458363/1000000000000 : ℝ) (294242864589/500000000000 : ℝ) (294242864591/500000000000 : ℝ) (105169939371/250000000000 : ℝ) (105169939373/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 1 (294242864589/500000000000 : ℝ) (294242864591/500000000000 : ℝ) (105169939371/250000000000 : ℝ) (105169939373/250000000000 : ℝ) (504582743331/1000000000000 : ℝ) (504582743337/1000000000000 : ℝ) (99511614163/200000000000 : ℝ) (248779035411/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 2 (504582743331/1000000000000 : ℝ) (504582743337/1000000000000 : ℝ) (99511614163/200000000000 : ℝ) (248779035411/500000000000 : ℝ) (501070407073/1000000000000 : ℝ) (12526760177/25000000000 : ℝ) (501058096769/1000000000000 : ℝ) (501058096777/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 3 (501070407073/1000000000000 : ℝ) (12526760177/25000000000 : ℝ) (501058096769/1000000000000 : ℝ) (501058096777/1000000000000 : ℝ) (501064251921/1000000000000 : ℝ) (501064251929/1000000000000 : ℝ) (501064251883/1000000000000 : ℝ) (501064251891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 4 (501064251921/1000000000000 : ℝ) (501064251929/1000000000000 : ℝ) (501064251883/1000000000000 : ℝ) (501064251891/1000000000000 : ℝ) (250532125951/500000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 5 (250532125951/500000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 6 (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66731/524288 : ℝ))) 7 (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66731/524288 : ℝ)) hmem 8 (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66731/524288 : ℝ))) hcmem 8 (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66731/524288 : ℝ)) (992092296817/1000000000000 : ℝ) (49604614841/50000000000 : ℝ) (501064251901/1000000000000 : ℝ) (50106425191/100000000000 : ℝ) (158668682117/200000000000 : ℝ) (396671705301/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0658_exp_lower
  have heNumeric : (2054902342221/1000000000000 : ℝ)/4 ≤ Real.exp (-42628226325403/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902342221/1000000000000 : ℝ)/4 ≤ Real.exp ((33365/262144 : ℝ)-(396671705301/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33365/262144 : ℝ) (66731/524288 : ℝ) (396671705301/500000000000 : ℝ) (2054902342221/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0659; no trusted numerical premise.
theorem cover8_leaf0659_exp_radius : (998013207712307053/1000000000000000000 : ℝ) ≤ Real.exp ((-16683/1048576 : ℝ)/8) ∧ Real.exp ((-16683/1048576 : ℝ)/8) ≤ (499006603856153527/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16683/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0659_exp_lower : (920113492596545067/1000000000000000000 : ℝ) ≤ Real.exp ((-85256453150181/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256453150181/128000000000000 : ℝ)/8) ≤ (230028373149136267/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256453150181/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0659_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725583551/250000000000 : ℝ) ≤ 4*Real.exp (66731/524288 : ℝ)*Real.exp (-mu (radius 8 (16683/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725583551/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16683/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0659_exp_radius
  have hrNumeric : (39368629969/40000000000 : ℝ) ≤ Real.exp (-16683/1048576 : ℝ) ∧ Real.exp (-16683/1048576 : ℝ) ≤ (492107874613/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39368629969/40000000000 : ℝ) ≤ (radius 8 (16683/131072 : ℝ)) ∧ (radius 8 (16683/131072 : ℝ)) ≤ (492107874613/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16683/131072 : ℝ)) (39368629969/40000000000 : ℝ) (492107874613/500000000000 : ℝ) (176972763371/1000000000000 : ℝ) (88486381689/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16683/131072 : ℝ)) (39368629969/40000000000 : ℝ) (492107874613/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39368629969/40000000000 : ℝ) (492107874613/500000000000 : ℝ) (248026968653/250000000000 : ℝ) (992107874613/1000000000000 : ℝ) (248019120889/250000000000 : ℝ) (992076483557/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 1 (248026968653/250000000000 : ℝ) (992107874613/1000000000000 : ℝ) (248019120889/250000000000 : ℝ) (992076483557/1000000000000 : ℝ) (248023044771/250000000000 : ℝ) (198418435817/200000000000 : ℝ) (992092178959/1000000000000 : ℝ) (992092178961/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 2 (248023044771/250000000000 : ℝ) (198418435817/200000000000 : ℝ) (992092178959/1000000000000 : ℝ) (992092178961/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 3 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 4 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 5 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 6 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16683/131072 : ℝ)) 7 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16683/131072 : ℝ))) (176972763371/1000000000000 : ℝ) (88486381689/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176972763371/1000000000000 : ℝ) (88486381689/500000000000 : ℝ) (117697276337/200000000000 : ℝ) (588486381689/1000000000000 : ℝ) (420681308559/1000000000000 : ℝ) (52585163571/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 1 (117697276337/200000000000 : ℝ) (588486381689/1000000000000 : ℝ) (420681308559/1000000000000 : ℝ) (52585163571/125000000000 : ℝ) (252291922561/500000000000 : ℝ) (504583845129/1000000000000 : ℝ) (497559263923/1000000000000 : ℝ) (497559263931/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 2 (252291922561/500000000000 : ℝ) (504583845129/1000000000000 : ℝ) (497559263923/1000000000000 : ℝ) (497559263931/1000000000000 : ℝ) (250535777261/500000000000 : ℝ) (50107155453/100000000000 : ℝ) (501059244567/1000000000000 : ℝ) (20042369783/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 3 (250535777261/500000000000 : ℝ) (50107155453/100000000000 : ℝ) (501059244567/1000000000000 : ℝ) (20042369783/40000000000 : ℝ) (62633174943/125000000000 : ℝ) (501065399553/1000000000000 : ℝ) (250532699753/500000000000 : ℝ) (100213079903/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 4 (62633174943/125000000000 : ℝ) (501065399553/1000000000000 : ℝ) (250532699753/500000000000 : ℝ) (100213079903/200000000000 : ℝ) (20042615981/40000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 5 (20042615981/40000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 6 (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16683/131072 : ℝ))) 7 (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16683/131072 : ℝ)) hmem 8 (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16683/131072 : ℝ))) hcmem 8 (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16683/131072 : ℝ)) (992092179021/1000000000000 : ℝ) (992092179023/1000000000000 : ℝ) (125266349881/250000000000 : ℝ) (250532699767/500000000000 : ℝ) (396672660917/500000000000 : ℝ) (198336330463/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0659_exp_lower
  have heNumeric : (513725583551/250000000000 : ℝ)/4 ≤ Real.exp (-85256453150181/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725583551/250000000000 : ℝ)/4 ≤ Real.exp ((66731/524288 : ℝ)-(198336330463/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66731/524288 : ℝ) (16683/131072 : ℝ) (198336330463/250000000000 : ℝ) (513725583551/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0660; no trusted numerical premise.
theorem cover8_leaf0660_exp_radius : (998013177969196133/1000000000000000000 : ℝ) ≤ Real.exp ((-66733/4194304 : ℝ)/8) ∧ Real.exp ((-66733/4194304 : ℝ)/8) ≤ (499006588984598067/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66733/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0660_exp_lower : (184022698429796527/200000000000000000 : ℝ) ≤ Real.exp ((-21314113412069/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314113412069/32000000000000 : ℝ)/8) ≤ (230028373037245659/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314113412069/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0660_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902326207/1000000000000 : ℝ) ≤ 4*Real.exp (16683/131072 : ℝ)*Real.exp (-mu (radius 8 (66733/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902326207/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66733/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0660_exp_radius
  have hrNumeric : (984215514569/1000000000000 : ℝ) ≤ Real.exp (-66733/4194304 : ℝ) ∧ Real.exp (-66733/4194304 : ℝ) ≤ (98421551457/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984215514569/1000000000000 : ℝ) ≤ (radius 8 (66733/524288 : ℝ)) ∧ (radius 8 (66733/524288 : ℝ)) ≤ (98421551457/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66733/524288 : ℝ)) (984215514569/1000000000000 : ℝ) (98421551457/100000000000 : ℝ) (88487034191/500000000000 : ℝ) (44243517097/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66733/524288 : ℝ)) (984215514569/1000000000000 : ℝ) (98421551457/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984215514569/1000000000000 : ℝ) (98421551457/100000000000 : ℝ) (248026939321/250000000000 : ℝ) (198421551457/200000000000 : ℝ) (99207636529/100000000000 : ℝ) (248019091323/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 1 (248026939321/250000000000 : ℝ) (198421551457/200000000000 : ℝ) (99207636529/100000000000 : ℝ) (248019091323/250000000000 : ℝ) (992092061287/1000000000000 : ℝ) (992092061289/1000000000000 : ℝ) (496046030581/500000000000 : ℝ) (198418412233/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 2 (992092061287/1000000000000 : ℝ) (992092061289/1000000000000 : ℝ) (496046030581/500000000000 : ℝ) (198418412233/200000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 3 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 4 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 5 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 6 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66733/524288 : ℝ)) 7 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66733/524288 : ℝ))) (88487034191/500000000000 : ℝ) (44243517097/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88487034191/500000000000 : ℝ) (44243517097/250000000000 : ℝ) (588487034191/1000000000000 : ℝ) (294243517097/500000000000 : ℝ) (52585357453/125000000000 : ℝ) (26292678727/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 1 (588487034191/1000000000000 : ℝ) (294243517097/500000000000 : ℝ) (52585357453/125000000000 : ℝ) (26292678727/62500000000 : ℝ) (504584946907/1000000000000 : ℝ) (504584946913/1000000000000 : ℝ) (19902418281/40000000000 : ℝ) (62195057129/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 2 (504584946907/1000000000000 : ℝ) (504584946913/1000000000000 : ℝ) (19902418281/40000000000 : ℝ) (62195057129/125000000000 : ℝ) (250536350983/500000000000 : ℝ) (501072701973/1000000000000 : ℝ) (501060392359/1000000000000 : ℝ) (250530196183/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 3 (250536350983/500000000000 : ℝ) (501072701973/1000000000000 : ℝ) (501060392359/1000000000000 : ℝ) (250530196183/500000000000 : ℝ) (250533273581/500000000000 : ℝ) (50106654717/100000000000 : ℝ) (125266636781/250000000000 : ℝ) (125266636783/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 4 (250533273581/500000000000 : ℝ) (50106654717/100000000000 : ℝ) (125266636781/250000000000 : ℝ) (125266636783/250000000000 : ℝ) (501066547143/1000000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 5 (501066547143/1000000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 6 (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66733/524288 : ℝ))) 7 (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66733/524288 : ℝ)) hmem 8 (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66733/524288 : ℝ))) hcmem 8 (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66733/524288 : ℝ)) (124011507653/125000000000 : ℝ) (992092061227/1000000000000 : ℝ) (250533273571/500000000000 : ℝ) (501066547151/1000000000000 : ℝ) (31733889323/40000000000 : ℝ) (198336808273/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0660_exp_lower
  have heNumeric : (2054902326207/1000000000000 : ℝ)/4 ≤ Real.exp (-21314113412069/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902326207/1000000000000 : ℝ)/4 ≤ Real.exp ((16683/131072 : ℝ)-(198336808273/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16683/131072 : ℝ) (66733/524288 : ℝ) (198336808273/250000000000 : ℝ) (2054902326207/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0661; no trusted numerical premise.
theorem cover8_leaf0661_exp_radius : (998013148226086099/1000000000000000000 : ℝ) ≤ Real.exp ((-33367/2097152 : ℝ)/8) ∧ Real.exp ((-33367/2097152 : ℝ)/8) ≤ (9980131482260861/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33367/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0661_exp_lower : (460056745852147779/500000000000000000 : ℝ) ≤ Real.exp ((-85256454143171/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256454143171/128000000000000 : ℝ)/8) ≤ (920113491704295559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256454143171/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0661_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451159131/500000000000 : ℝ) ≤ 4*Real.exp (66733/524288 : ℝ)*Real.exp (-mu (radius 8 (33367/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451159131/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33367/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0661_exp_radius
  have hrNumeric : (492107639957/500000000000 : ℝ) ≤ Real.exp (-33367/2097152 : ℝ) ∧ Real.exp (-33367/2097152 : ℝ) ≤ (196843055983/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492107639957/500000000000 : ℝ) ≤ (radius 8 (33367/262144 : ℝ)) ∧ (radius 8 (33367/262144 : ℝ)) ≤ (196843055983/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33367/262144 : ℝ)) (492107639957/500000000000 : ℝ) (196843055983/200000000000 : ℝ) (2765240209/15625000000 : ℝ) (176975373383/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33367/262144 : ℝ)) (492107639957/500000000000 : ℝ) (196843055983/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492107639957/500000000000 : ℝ) (196843055983/200000000000 : ℝ) (992107639957/1000000000000 : ℝ) (496053819979/500000000000 : ℝ) (496038123513/500000000000 : ℝ) (992076247027/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 1 (992107639957/1000000000000 : ℝ) (496053819979/500000000000 : ℝ) (496038123513/500000000000 : ℝ) (992076247027/1000000000000 : ℝ) (992091943491/1000000000000 : ℝ) (992091943493/1000000000000 : ℝ) (992091943367/1000000000000 : ℝ) (992091943369/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 2 (992091943491/1000000000000 : ℝ) (992091943493/1000000000000 : ℝ) (992091943367/1000000000000 : ℝ) (992091943369/1000000000000 : ℝ) (992091943429/1000000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 3 (992091943429/1000000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 4 (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 5 (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 6 (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33367/262144 : ℝ)) 7 (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33367/262144 : ℝ))) (2765240209/15625000000 : ℝ) (176975373383/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2765240209/15625000000 : ℝ) (176975373383/1000000000000 : ℝ) (18390240209/31250000000 : ℝ) (147121921673/250000000000 : ℝ) (52585551333/125000000000 : ℝ) (420684410673/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 1 (18390240209/31250000000 : ℝ) (147121921673/250000000000 : ℝ) (52585551333/125000000000 : ℝ) (420684410673/1000000000000 : ℝ) (126146512169/250000000000 : ℝ) (504586048683/1000000000000 : ℝ) (497561650107/1000000000000 : ℝ) (99512330023/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 2 (126146512169/250000000000 : ℝ) (504586048683/1000000000000 : ℝ) (497561650107/1000000000000 : ℝ) (99512330023/200000000000 : ℝ) (501073849391/1000000000000 : ℝ) (501073849399/1000000000000 : ℝ) (125265385033/250000000000 : ℝ) (501061540141/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 3 (501073849391/1000000000000 : ℝ) (501073849399/1000000000000 : ℝ) (125265385033/250000000000 : ℝ) (501061540141/1000000000000 : ℝ) (501067694761/1000000000000 : ℝ) (50106769477/100000000000 : ℝ) (501067694723/1000000000000 : ℝ) (501067694733/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 4 (501067694761/1000000000000 : ℝ) (50106769477/100000000000 : ℝ) (501067694723/1000000000000 : ℝ) (501067694733/1000000000000 : ℝ) (250533847371/500000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 5 (250533847371/500000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 6 (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33367/262144 : ℝ))) 7 (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33367/262144 : ℝ)) hmem 8 (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33367/262144 : ℝ))) hcmem 8 (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33367/262144 : ℝ)) (248022985857/250000000000 : ℝ) (992091943431/1000000000000 : ℝ) (501067694741/1000000000000 : ℝ) (15658365461/31250000000 : ℝ) (396674572143/500000000000 : ℝ) (793349144307/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0661_exp_lower
  have heNumeric : (1027451159131/500000000000 : ℝ)/4 ≤ Real.exp (-85256454143171/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451159131/500000000000 : ℝ)/4 ≤ Real.exp ((66733/524288 : ℝ)-(793349144307/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66733/524288 : ℝ) (33367/262144 : ℝ) (793349144307/1000000000000 : ℝ) (1027451159131/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0662; no trusted numerical premise.
theorem cover8_leaf0662_exp_radius : (998013118482976951/1000000000000000000 : ℝ) ≤ Real.exp ((-66735/4194304 : ℝ)/8) ∧ Real.exp ((-66735/4194304 : ℝ)/8) ≤ (124751639810372119/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66735/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0662_exp_lower : (460056745631069397/500000000000000000 : ℝ) ≤ Real.exp ((-341025818541/512000000000 : ℝ)/8) ∧ Real.exp ((-341025818541/512000000000 : ℝ)/8) ≤ (184022698252427759/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341025818541/512000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0662_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451155181/500000000000 : ℝ) ≤ 4*Real.exp (33367/262144 : ℝ)*Real.exp (-mu (radius 8 (66735/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451155181/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66735/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0662_exp_radius
  have hrNumeric : (984215045259/1000000000000 : ℝ) ≤ Real.exp (-66735/4194304 : ℝ) ∧ Real.exp (-66735/4194304 : ℝ) ≤ (49210752263/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984215045259/1000000000000 : ℝ) ≤ (radius 8 (66735/524288 : ℝ)) ∧ (radius 8 (66735/524288 : ℝ)) ≤ (49210752263/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66735/524288 : ℝ)) (984215045259/1000000000000 : ℝ) (49210752263/50000000000 : ℝ) (176976678361/1000000000000 : ℝ) (5530521199/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66735/524288 : ℝ)) (984215045259/1000000000000 : ℝ) (49210752263/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984215045259/1000000000000 : ℝ) (49210752263/50000000000 : ℝ) (992107522629/1000000000000 : ℝ) (99210752263/100000000000 : ℝ) (992076128761/1000000000000 : ℝ) (992076128763/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 1 (992107522629/1000000000000 : ℝ) (99210752263/100000000000 : ℝ) (992076128761/1000000000000 : ℝ) (992076128763/1000000000000 : ℝ) (198418365139/200000000000 : ℝ) (992091825697/1000000000000 : ℝ) (99209182557/100000000000 : ℝ) (992091825573/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 2 (198418365139/200000000000 : ℝ) (992091825697/1000000000000 : ℝ) (99209182557/100000000000 : ℝ) (992091825573/1000000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 3 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 4 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 5 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 6 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66735/524288 : ℝ)) 7 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66735/524288 : ℝ))) (176976678361/1000000000000 : ℝ) (5530521199/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176976678361/1000000000000 : ℝ) (5530521199/31250000000 : ℝ) (29424416959/50000000000 : ℝ) (36780521199/62500000000 : ℝ) (420685961687/1000000000000 : ℝ) (13146436303/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 1 (29424416959/50000000000 : ℝ) (36780521199/62500000000 : ℝ) (420685961687/1000000000000 : ℝ) (13146436303/31250000000 : ℝ) (504587150433/1000000000000 : ℝ) (12614678761/25000000000 : ℝ) (62195355397/125000000000 : ℝ) (31097677699/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 2 (504587150433/1000000000000 : ℝ) (12614678761/25000000000 : ℝ) (62195355397/125000000000 : ℝ) (31097677699/62500000000 : ℝ) (125268749201/250000000000 : ℝ) (125268749203/250000000000 : ℝ) (501062687893/1000000000000 : ℝ) (250531343951/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 3 (125268749201/250000000000 : ℝ) (125268749203/250000000000 : ℝ) (501062687893/1000000000000 : ℝ) (250531343951/500000000000 : ℝ) (125267210587/250000000000 : ℝ) (501068842357/1000000000000 : ℝ) (50106884231/100000000000 : ℝ) (6263360529/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 4 (125267210587/250000000000 : ℝ) (501068842357/1000000000000 : ℝ) (50106884231/100000000000 : ℝ) (6263360529/12500000000 : ℝ) (501068842329/1000000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 5 (501068842329/1000000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 6 (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66735/524288 : ℝ))) 7 (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66735/524288 : ℝ)) hmem 8 (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66735/524288 : ℝ))) hcmem 8 (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66735/524288 : ℝ)) (31002869551/31250000000 : ℝ) (198418365127/200000000000 : ℝ) (62633605291/125000000000 : ℝ) (501068842339/1000000000000 : ℝ) (793351055479/1000000000000 : ℝ) (1586702111/2000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0662_exp_lower
  have heNumeric : (1027451155181/500000000000 : ℝ)/4 ≤ Real.exp (-341025818541/512000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451155181/500000000000 : ℝ)/4 ≤ Real.exp ((33367/262144 : ℝ)-(1586702111/2000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33367/262144 : ℝ) (66735/524288 : ℝ) (1586702111/2000000000 : ℝ) (1027451155181/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0663; no trusted numerical premise.
theorem cover8_leaf0663_exp_radius : (99801308873986869/100000000000000000 : ℝ) ≤ Real.exp ((-4171/262144 : ℝ)/8) ∧ Real.exp ((-4171/262144 : ℝ)/8) ≤ (998013088739868691/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4171/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0663_exp_lower : (920113490822167299/1000000000000000000 : ℝ) ≤ Real.exp ((-85256455124897/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256455124897/128000000000000 : ℝ)/8) ≤ (9201134908221673/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256455124897/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0663_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451151251/500000000000 : ℝ) ≤ 4*Real.exp (66735/524288 : ℝ)*Real.exp (-mu (radius 8 (4171/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451151251/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4171/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0663_exp_radius
  have hrNumeric : (246053702651/250000000000 : ℝ) ≤ Real.exp (-4171/262144 : ℝ) ∧ Real.exp (-4171/262144 : ℝ) ≤ (196842962121/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246053702651/250000000000 : ℝ) ≤ (radius 8 (4171/32768 : ℝ)) ∧ (radius 8 (4171/32768 : ℝ)) ≤ (196842962121/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4171/32768 : ℝ)) (246053702651/250000000000 : ℝ) (196842962121/200000000000 : ℝ) (22122247917/125000000000 : ℝ) (88488991671/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4171/32768 : ℝ)) (246053702651/250000000000 : ℝ) (196842962121/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246053702651/250000000000 : ℝ) (196842962121/200000000000 : ℝ) (496053702651/500000000000 : ℝ) (992107405303/1000000000000 : ℝ) (992076010497/1000000000000 : ℝ) (496038005249/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 1 (496053702651/500000000000 : ℝ) (992107405303/1000000000000 : ℝ) (992076010497/1000000000000 : ℝ) (496038005249/500000000000 : ℝ) (992091707899/1000000000000 : ℝ) (992091707901/1000000000000 : ℝ) (39683668311/40000000000 : ℝ) (992091707777/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 2 (992091707899/1000000000000 : ℝ) (992091707901/1000000000000 : ℝ) (39683668311/40000000000 : ℝ) (992091707777/1000000000000 : ℝ) (992091707837/1000000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 3 (992091707837/1000000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 4 (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 5 (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 6 (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4171/32768 : ℝ)) 7 (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4171/32768 : ℝ))) (22122247917/125000000000 : ℝ) (88488991671/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22122247917/125000000000 : ℝ) (88488991671/500000000000 : ℝ) (147122247917/250000000000 : ℝ) (588488991671/1000000000000 : ℝ) (420687512693/1000000000000 : ℝ) (420687512701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 1 (147122247917/250000000000 : ℝ) (588488991671/1000000000000 : ℝ) (420687512693/1000000000000 : ℝ) (420687512701/1000000000000 : ℝ) (25229412609/50000000000 : ℝ) (252294126093/500000000000 : ℝ) (62195504529/125000000000 : ℝ) (497564036239/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 2 (25229412609/50000000000 : ℝ) (252294126093/500000000000 : ℝ) (62195504529/125000000000 : ℝ) (497564036239/1000000000000 : ℝ) (250538072103/500000000000 : ℝ) (501076144213/1000000000000 : ℝ) (501063835643/1000000000000 : ℝ) (501063835651/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 3 (250538072103/500000000000 : ℝ) (501076144213/1000000000000 : ℝ) (501063835643/1000000000000 : ℝ) (501063835651/1000000000000 : ℝ) (125267497481/250000000000 : ℝ) (125267497483/250000000000 : ℝ) (250534994943/500000000000 : ℝ) (100213997979/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 4 (125267497481/250000000000 : ℝ) (125267497483/250000000000 : ℝ) (250534994943/500000000000 : ℝ) (100213997979/200000000000 : ℝ) (100213997981/200000000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 5 (100213997981/200000000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 6 (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4171/32768 : ℝ))) 7 (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4171/32768 : ℝ)) hmem 8 (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4171/32768 : ℝ))) hcmem 8 (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4171/32768 : ℝ)) (248022926959/250000000000 : ℝ) (992091707839/1000000000000 : ℝ) (31316874369/62500000000 : ℝ) (250534994957/500000000000 : ℝ) (158670593331/200000000000 : ℝ) (396676483337/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0663_exp_lower
  have heNumeric : (1027451151251/500000000000 : ℝ)/4 ≤ Real.exp (-85256455124897/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451151251/500000000000 : ℝ)/4 ≤ Real.exp ((66735/524288 : ℝ)-(396676483337/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66735/524288 : ℝ) (4171/32768 : ℝ) (396676483337/500000000000 : ℝ) (1027451151251/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0664; no trusted numerical premise.
theorem cover8_leaf0664_exp_radius : (249503264749190329/250000000000000000 : ℝ) ≤ Real.exp ((-66737/4194304 : ℝ)/8) ∧ Real.exp ((-66737/4194304 : ℝ)/8) ≤ (998013058996761317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66737/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0664_exp_lower : (46005674519213303/50000000000000000 : ℝ) ≤ Real.exp ((-1065705695153/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065705695153/1600000000000 : ℝ)/8) ≤ (920113490384266061/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065705695153/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0664_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451147339/500000000000 : ℝ) ≤ 4*Real.exp (4171/32768 : ℝ)*Real.exp (-mu (radius 8 (66737/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451147339/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66737/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0664_exp_radius
  have hrNumeric : (984214575949/1000000000000 : ℝ) ≤ Real.exp (-66737/4194304 : ℝ) ∧ Real.exp (-66737/4194304 : ℝ) ≤ (19684291519/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984214575949/1000000000000 : ℝ) ≤ (radius 8 (66737/524288 : ℝ)) ∧ (radius 8 (66737/524288 : ℝ)) ≤ (19684291519/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66737/524288 : ℝ)) (984214575949/1000000000000 : ℝ) (19684291519/20000000000 : ℝ) (176979288301/1000000000000 : ℝ) (176979288307/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66737/524288 : ℝ)) (984214575949/1000000000000 : ℝ) (19684291519/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984214575949/1000000000000 : ℝ) (19684291519/20000000000 : ℝ) (496053643987/500000000000 : ℝ) (39684291519/40000000000 : ℝ) (124009486529/125000000000 : ℝ) (496037946117/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 1 (496053643987/500000000000 : ℝ) (39684291519/40000000000 : ℝ) (124009486529/125000000000 : ℝ) (496037946117/500000000000 : ℝ) (992091590103/1000000000000 : ℝ) (198418318021/200000000000 : ℝ) (496045794989/500000000000 : ℝ) (992091589981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 2 (992091590103/1000000000000 : ℝ) (198418318021/200000000000 : ℝ) (496045794989/500000000000 : ℝ) (992091589981/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 3 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 4 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 5 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 6 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66737/524288 : ℝ)) 7 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66737/524288 : ℝ))) (176979288301/1000000000000 : ℝ) (176979288307/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176979288301/1000000000000 : ℝ) (176979288307/1000000000000 : ℝ) (11769792883/20000000000 : ℝ) (294244822077/500000000000 : ℝ) (420689063681/1000000000000 : ℝ) (420689063689/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 1 (11769792883/20000000000 : ℝ) (294244822077/500000000000 : ℝ) (420689063681/1000000000000 : ℝ) (420689063689/1000000000000 : ℝ) (100917870783/200000000000 : ℝ) (252294676961/500000000000 : ℝ) (248782614637/500000000000 : ℝ) (248782614641/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 2 (100917870783/200000000000 : ℝ) (252294676961/500000000000 : ℝ) (248782614637/500000000000 : ℝ) (248782614641/500000000000 : ℝ) (250538645797/500000000000 : ℝ) (250538645801/500000000000 : ℝ) (25053249169/50000000000 : ℝ) (125266245847/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 3 (250538645797/500000000000 : ℝ) (250538645801/500000000000 : ℝ) (25053249169/50000000000 : ℝ) (125266245847/250000000000 : ℝ) (501071137487/1000000000000 : ℝ) (100214227499/200000000000 : ℝ) (501071137449/1000000000000 : ℝ) (250535568729/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 4 (501071137487/1000000000000 : ℝ) (100214227499/200000000000 : ℝ) (501071137449/1000000000000 : ℝ) (250535568729/500000000000 : ℝ) (125267784367/250000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 5 (125267784367/250000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 6 (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66737/524288 : ℝ))) 7 (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66737/524288 : ℝ)) hmem 8 (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66737/524288 : ℝ))) hcmem 8 (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66737/524288 : ℝ)) (24802289751/25000000000 : ℝ) (992091590043/1000000000000 : ℝ) (501071137467/1000000000000 : ℝ) (501071137477/1000000000000 : ℝ) (793354877811/1000000000000 : ℝ) (79335487783/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0664_exp_lower
  have heNumeric : (1027451147339/500000000000 : ℝ)/4 ≤ Real.exp (-1065705695153/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451147339/500000000000 : ℝ)/4 ≤ Real.exp ((4171/32768 : ℝ)-(79335487783/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4171/32768 : ℝ) (66737/524288 : ℝ) (79335487783/100000000000 : ℝ) (1027451147339/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0665; no trusted numerical premise.
theorem cover8_leaf0665_exp_radius : (249503257313413707/250000000000000000 : ℝ) ≤ Real.exp ((-33369/2097152 : ℝ)/8) ∧ Real.exp ((-33369/2097152 : ℝ)/8) ≤ (998013029253654829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33369/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0665_exp_lower : (184022697989733021/200000000000000000 : ℝ) ≤ Real.exp ((-85256456097023/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256456097023/128000000000000 : ℝ)/8) ≤ (460056744974332553/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256456097023/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0665_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980457379/200000000000 : ℝ) ≤ 4*Real.exp (66737/524288 : ℝ)*Real.exp (-mu (radius 8 (33369/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980457379/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33369/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0665_exp_radius
  have hrNumeric : (492107170647/500000000000 : ℝ) ≤ Real.exp (-33369/2097152 : ℝ) ∧ Real.exp (-33369/2097152 : ℝ) ≤ (196842868259/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492107170647/500000000000 : ℝ) ≤ (radius 8 (33369/262144 : ℝ)) ∧ (radius 8 (33369/262144 : ℝ)) ≤ (196842868259/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33369/262144 : ℝ)) (492107170647/500000000000 : ℝ) (196842868259/200000000000 : ℝ) (22122574157/125000000000 : ℝ) (88490296631/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33369/262144 : ℝ)) (492107170647/500000000000 : ℝ) (196842868259/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492107170647/500000000000 : ℝ) (196842868259/200000000000 : ℝ) (992107170647/1000000000000 : ℝ) (124013396331/125000000000 : ℝ) (992075773967/1000000000000 : ℝ) (992075773969/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 1 (992107170647/1000000000000 : ℝ) (124013396331/125000000000 : ℝ) (992075773967/1000000000000 : ℝ) (992075773969/1000000000000 : ℝ) (992091472307/1000000000000 : ℝ) (992091472309/1000000000000 : ℝ) (496045736091/500000000000 : ℝ) (198418294437/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 2 (992091472307/1000000000000 : ℝ) (992091472309/1000000000000 : ℝ) (496045736091/500000000000 : ℝ) (198418294437/200000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 3 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 4 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 5 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 6 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33369/262144 : ℝ)) 7 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33369/262144 : ℝ))) (22122574157/125000000000 : ℝ) (88490296631/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22122574157/125000000000 : ℝ) (88490296631/500000000000 : ℝ) (147122574157/250000000000 : ℝ) (588490296631/1000000000000 : ℝ) (420690614651/1000000000000 : ℝ) (420690614659/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 1 (147122574157/250000000000 : ℝ) (588490296631/1000000000000 : ℝ) (420690614651/1000000000000 : ℝ) (420690614659/1000000000000 : ℝ) (504590455639/1000000000000 : ℝ) (100918091129/200000000000 : ℝ) (15548950697/31250000000 : ℝ) (497566422311/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 2 (504590455639/1000000000000 : ℝ) (100918091129/200000000000 : ℝ) (15548950697/31250000000 : ℝ) (497566422311/1000000000000 : ℝ) (501078438971/1000000000000 : ℝ) (250539219489/500000000000 : ℝ) (100213226221/200000000000 : ℝ) (501066131113/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 3 (501078438971/1000000000000 : ℝ) (250539219489/500000000000 : ℝ) (100213226221/200000000000 : ℝ) (501066131113/1000000000000 : ℝ) (250536142519/500000000000 : ℝ) (250536142523/500000000000 : ℝ) (100214457/200000000 : ℝ) (31317017813/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 4 (250536142519/500000000000 : ℝ) (250536142523/500000000000 : ℝ) (100214457/200000000 : ℝ) (31317017813/62500000000 : ℝ) (501072285019/1000000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 5 (501072285019/1000000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 6 (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33369/262144 : ℝ))) 7 (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33369/262144 : ℝ)) hmem 8 (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33369/262144 : ℝ))) hcmem 8 (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33369/262144 : ℝ)) (248022868061/250000000000 : ℝ) (992091472247/1000000000000 : ℝ) (250536142509/500000000000 : ℝ) (501072285027/1000000000000 : ℝ) (198339197237/250000000000 : ℝ) (396678394483/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0665_exp_lower
  have heNumeric : (410980457379/200000000000 : ℝ)/4 ≤ Real.exp (-85256456097023/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980457379/200000000000 : ℝ)/4 ≤ Real.exp ((66737/524288 : ℝ)-(396678394483/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66737/524288 : ℝ) (33369/262144 : ℝ) (396678394483/500000000000 : ℝ) (410980457379/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0666; no trusted numerical premise.
theorem cover8_leaf0666_exp_radius : (499006499755274613/500000000000000000 : ℝ) ≤ Real.exp ((-66739/4194304 : ℝ)/8) ∧ Real.exp ((-66739/4194304 : ℝ)/8) ≤ (998012999510549227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66739/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0666_exp_lower : (184022697903026881/200000000000000000 : ℝ) ≤ Real.exp ((-42628228289751/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628228289751/64000000000000 : ℝ)/8) ≤ (460056744757567203/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628228289751/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0666_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098045583/20000000000 : ℝ) ≤ 4*Real.exp (33369/262144 : ℝ)*Real.exp (-mu (radius 8 (66739/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (41098045583/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66739/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0666_exp_radius
  have hrNumeric : (984214106639/1000000000000 : ℝ) ≤ Real.exp (-66739/4194304 : ℝ) ∧ Real.exp (-66739/4194304 : ℝ) ≤ (12302676333/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984214106639/1000000000000 : ℝ) ≤ (radius 8 (66739/524288 : ℝ)) ∧ (radius 8 (66739/524288 : ℝ)) ≤ (12302676333/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66739/524288 : ℝ)) (984214106639/1000000000000 : ℝ) (12302676333/12500000000 : ℝ) (884909491/5000000000 : ℝ) (176981898207/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66739/524288 : ℝ)) (984214106639/1000000000000 : ℝ) (12302676333/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984214106639/1000000000000 : ℝ) (12302676333/12500000000 : ℝ) (992107053319/1000000000000 : ℝ) (24802676333/25000000000 : ℝ) (992075655703/1000000000000 : ℝ) (124009456963/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 1 (992107053319/1000000000000 : ℝ) (24802676333/25000000000 : ℝ) (992075655703/1000000000000 : ℝ) (124009456963/125000000000 : ℝ) (992091354511/1000000000000 : ℝ) (62005709657/62500000000 : ℝ) (496045677193/500000000000 : ℝ) (248022838597/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 2 (992091354511/1000000000000 : ℝ) (62005709657/62500000000 : ℝ) (496045677193/500000000000 : ℝ) (248022838597/250000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 3 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 4 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 5 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 6 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66739/524288 : ℝ)) 7 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66739/524288 : ℝ))) (884909491/5000000000 : ℝ) (176981898207/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (884909491/5000000000 : ℝ) (176981898207/1000000000000 : ℝ) (5884909491/10000000000 : ℝ) (36780684319/62500000000 : ℝ) (420692165603/1000000000000 : ℝ) (105173041403/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 1 (5884909491/10000000000 : ℝ) (36780684319/62500000000 : ℝ) (420692165603/1000000000000 : ℝ) (105173041403/250000000000 : ℝ) (504591557351/1000000000000 : ℝ) (252295778679/500000000000 : ℝ) (497567615319/1000000000000 : ℝ) (497567615327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 2 (504591557351/1000000000000 : ℝ) (252295778679/500000000000 : ℝ) (497567615319/1000000000000 : ℝ) (497567615327/1000000000000 : ℝ) (100215917267/200000000000 : ℝ) (501079586343/1000000000000 : ℝ) (501067278817/1000000000000 : ℝ) (20042691153/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 3 (100215917267/200000000000 : ℝ) (501079586343/1000000000000 : ℝ) (501067278817/1000000000000 : ℝ) (20042691153/40000000000 : ℝ) (122332381/244140625 : ℝ) (62634179073/125000000000 : ℝ) (250536716269/500000000000 : ℝ) (501073432547/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 4 (122332381/244140625 : ℝ) (62634179073/125000000000 : ℝ) (250536716269/500000000000 : ℝ) (501073432547/1000000000000 : ℝ) (501073432557/1000000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 5 (501073432557/1000000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 6 (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66739/524288 : ℝ))) 7 (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66739/524288 : ℝ)) hmem 8 (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66739/524288 : ℝ))) hcmem 8 (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66739/524288 : ℝ)) (62005709653/62500000000 : ℝ) (19841827089/20000000000 : ℝ) (125268358139/250000000000 : ℝ) (250536716283/500000000000 : ℝ) (396679350033/500000000000 : ℝ) (198339675021/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0666_exp_lower
  have heNumeric : (41098045583/20000000000 : ℝ)/4 ≤ Real.exp (-42628228289751/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098045583/20000000000 : ℝ)/4 ≤ Real.exp ((33369/262144 : ℝ)-(198339675021/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33369/262144 : ℝ) (66739/524288 : ℝ) (198339675021/250000000000 : ℝ) (41098045583/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0667; no trusted numerical premise.
theorem cover8_leaf0667_exp_radius : (998012969767444511/1000000000000000000 : ℝ) ≤ Real.exp ((-16685/1048576 : ℝ)/8) ∧ Real.exp ((-16685/1048576 : ℝ)/8) ≤ (31187905305232641/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16685/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0667_exp_lower : (230028372271004751/250000000000000000 : ℝ) ≤ Real.exp ((-85256457059293/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256457059293/128000000000000 : ℝ)/8) ≤ (184022697816803801/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256457059293/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0667_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902271447/1000000000000 : ℝ) ≤ 4*Real.exp (66739/524288 : ℝ)*Real.exp (-mu (radius 8 (16685/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902271447/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16685/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0667_exp_radius
  have hrNumeric : (61513366999/62500000000 : ℝ) ≤ Real.exp (-16685/1048576 : ℝ) ∧ Real.exp (-16685/1048576 : ℝ) ≤ (196842774397/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61513366999/62500000000 : ℝ) ≤ (radius 8 (16685/131072 : ℝ)) ∧ (radius 8 (16685/131072 : ℝ)) ≤ (196842774397/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16685/131072 : ℝ)) (61513366999/62500000000 : ℝ) (196842774397/200000000000 : ℝ) (2765362549/15625000000 : ℝ) (88491601571/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16685/131072 : ℝ)) (61513366999/62500000000 : ℝ) (196842774397/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61513366999/62500000000 : ℝ) (196842774397/200000000000 : ℝ) (124013366999/125000000000 : ℝ) (992106935993/1000000000000 : ℝ) (496037768719/500000000000 : ℝ) (6200472109/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 1 (124013366999/125000000000 : ℝ) (992106935993/1000000000000 : ℝ) (496037768719/500000000000 : ℝ) (6200472109/6250000000 : ℝ) (198418247343/200000000000 : ℝ) (992091236717/1000000000000 : ℝ) (99209123659/100000000000 : ℝ) (992091236593/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 2 (198418247343/200000000000 : ℝ) (992091236717/1000000000000 : ℝ) (99209123659/100000000000 : ℝ) (992091236593/1000000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 3 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 4 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 5 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 6 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16685/131072 : ℝ)) 7 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16685/131072 : ℝ))) (2765362549/15625000000 : ℝ) (88491601571/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2765362549/15625000000 : ℝ) (88491601571/500000000000 : ℝ) (18390362549/31250000000 : ℝ) (588491601571/1000000000000 : ℝ) (420693716539/1000000000000 : ℝ) (420693716547/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 1 (18390362549/31250000000 : ℝ) (588491601571/1000000000000 : ℝ) (420693716539/1000000000000 : ℝ) (420693716547/1000000000000 : ℝ) (504592659053/1000000000000 : ℝ) (504592659059/1000000000000 : ℝ) (248784404161/500000000000 : ℝ) (497568808329/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 2 (504592659053/1000000000000 : ℝ) (504592659059/1000000000000 : ℝ) (248784404161/500000000000 : ℝ) (497568808329/1000000000000 : ℝ) (501080733687/1000000000000 : ℝ) (250540366847/500000000000 : ℝ) (501068426517/1000000000000 : ℝ) (20042737061/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 3 (501080733687/1000000000000 : ℝ) (250540366847/500000000000 : ℝ) (501068426517/1000000000000 : ℝ) (20042737061/40000000000 : ℝ) (250537290051/500000000000 : ℝ) (50107458011/100000000000 : ℝ) (15658580627/31250000000 : ℝ) (62634322509/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 4 (250537290051/500000000000 : ℝ) (50107458011/100000000000 : ℝ) (15658580627/31250000000 : ℝ) (62634322509/125000000000 : ℝ) (501074580083/1000000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 5 (501074580083/1000000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 6 (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16685/131072 : ℝ))) 7 (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16685/131072 : ℝ)) hmem 8 (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16685/131072 : ℝ))) hcmem 8 (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16685/131072 : ℝ)) (248022809163/250000000000 : ℝ) (198418247331/200000000000 : ℝ) (250537290041/500000000000 : ℝ) (501074580091/1000000000000 : ℝ) (198340152791/250000000000 : ℝ) (793360611181/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0667_exp_lower
  have heNumeric : (2054902271447/1000000000000 : ℝ)/4 ≤ Real.exp (-85256457059293/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902271447/1000000000000 : ℝ)/4 ≤ Real.exp ((66739/524288 : ℝ)-(793360611181/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66739/524288 : ℝ) (16685/131072 : ℝ) (793360611181/1000000000000 : ℝ) (2054902271447/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0668; no trusted numerical premise.
theorem cover8_leaf0668_exp_radius : (499006470012170341/500000000000000000 : ℝ) ≤ Real.exp ((-66741/4194304 : ℝ)/8) ∧ Real.exp ((-66741/4194304 : ℝ)/8) ≤ (998012940024340683/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66741/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0668_exp_lower : (920113488654513801/1000000000000000000 : ℝ) ≤ Real.exp ((-21314114384323/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314114384323/32000000000000 : ℝ)/8) ≤ (460056744327256901/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314114384323/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0668_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902263773/1000000000000 : ℝ) ≤ 4*Real.exp (16685/131072 : ℝ)*Real.exp (-mu (radius 8 (66741/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902263773/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66741/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0668_exp_radius
  have hrNumeric : (984213637329/1000000000000 : ℝ) ≤ Real.exp (-66741/4194304 : ℝ) ∧ Real.exp (-66741/4194304 : ℝ) ≤ (98421363733/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984213637329/1000000000000 : ℝ) ≤ (radius 8 (66741/524288 : ℝ)) ∧ (radius 8 (66741/524288 : ℝ)) ≤ (98421363733/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66741/524288 : ℝ)) (984213637329/1000000000000 : ℝ) (98421363733/100000000000 : ℝ) (176984508061/1000000000000 : ℝ) (176984508067/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66741/524288 : ℝ)) (984213637329/1000000000000 : ℝ) (98421363733/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984213637329/1000000000000 : ℝ) (98421363733/100000000000 : ℝ) (124013352333/125000000000 : ℝ) (198421363733/200000000000 : ℝ) (992075419173/1000000000000 : ℝ) (39683016767/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 1 (124013352333/125000000000 : ℝ) (198421363733/200000000000 : ℝ) (992075419173/1000000000000 : ℝ) (39683016767/40000000000 : ℝ) (496045559459/500000000000 : ℝ) (24802277973/25000000000 : ℝ) (496045559397/500000000000 : ℝ) (248022779699/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 2 (496045559459/500000000000 : ℝ) (24802277973/25000000000 : ℝ) (496045559397/500000000000 : ℝ) (248022779699/250000000000 : ℝ) (124011389857/125000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 3 (124011389857/125000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 4 (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 5 (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 6 (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66741/524288 : ℝ)) 7 (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66741/524288 : ℝ))) (176984508061/1000000000000 : ℝ) (176984508067/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176984508061/1000000000000 : ℝ) (176984508067/1000000000000 : ℝ) (58849225403/100000000000 : ℝ) (294246127017/500000000000 : ℝ) (420695267457/1000000000000 : ℝ) (84139053493/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 1 (58849225403/100000000000 : ℝ) (294246127017/500000000000 : ℝ) (420695267457/1000000000000 : ℝ) (84139053493/200000000000 : ℝ) (504593760743/1000000000000 : ℝ) (2018375043/4000000000 : ℝ) (497570001311/1000000000000 : ℝ) (497570001319/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 2 (504593760743/1000000000000 : ℝ) (2018375043/4000000000 : ℝ) (497570001311/1000000000000 : ℝ) (497570001319/1000000000000 : ℝ) (501081881027/1000000000000 : ℝ) (100216376207/200000000000 : ℝ) (100213914841/200000000000 : ℝ) (501069574213/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 3 (501081881027/1000000000000 : ℝ) (100216376207/200000000000 : ℝ) (100213914841/200000000000 : ℝ) (501069574213/1000000000000 : ℝ) (1957327061/3906250000 : ℝ) (62634465953/125000000000 : ℝ) (250537863789/500000000000 : ℝ) (501075727587/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 4 (1957327061/3906250000 : ℝ) (62634465953/125000000000 : ℝ) (250537863789/500000000000 : ℝ) (501075727587/1000000000000 : ℝ) (501075727597/1000000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 5 (501075727597/1000000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 6 (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66741/524288 : ℝ))) 7 (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66741/524288 : ℝ)) hmem 8 (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66741/524288 : ℝ))) hcmem 8 (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66741/524288 : ℝ)) (198418223771/200000000000 : ℝ) (496045559429/500000000000 : ℝ) (125268931899/250000000000 : ℝ) (250537863803/500000000000 : ℝ) (198340630561/250000000000 : ℝ) (99170315283/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0668_exp_lower
  have heNumeric : (2054902263773/1000000000000 : ℝ)/4 ≤ Real.exp (-21314114384323/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902263773/1000000000000 : ℝ)/4 ≤ Real.exp ((16685/131072 : ℝ)-(99170315283/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16685/131072 : ℝ) (66741/524288 : ℝ) (99170315283/125000000000 : ℝ) (2054902263773/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0669; no trusted numerical premise.
theorem cover8_leaf0669_exp_radius : (998012910281237739/1000000000000000000 : ℝ) ≤ Real.exp ((-33371/2097152 : ℝ)/8) ∧ Real.exp ((-33371/2097152 : ℝ)/8) ≤ (49900645514061887/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33371/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0669_exp_lower : (920113488227998967/1000000000000000000 : ℝ) ≤ Real.exp ((-85256458011963/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256458011963/128000000000000 : ℝ)/8) ≤ (115014186028499871/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256458011963/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0669_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902256153/1000000000000 : ℝ) ≤ 4*Real.exp (66741/524288 : ℝ)*Real.exp (-mu (radius 8 (33371/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902256153/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33371/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0669_exp_radius
  have hrNumeric : (492106701337/500000000000 : ℝ) ≤ Real.exp (-33371/2097152 : ℝ) ∧ Real.exp (-33371/2097152 : ℝ) ≤ (39368536107/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492106701337/500000000000 : ℝ) ≤ (radius 8 (33371/262144 : ℝ)) ∧ (radius 8 (33371/262144 : ℝ)) ≤ (39368536107/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33371/262144 : ℝ)) (492106701337/500000000000 : ℝ) (39368536107/40000000000 : ℝ) (11061613311/62500000000 : ℝ) (88492906491/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33371/262144 : ℝ)) (492106701337/500000000000 : ℝ) (39368536107/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492106701337/500000000000 : ℝ) (39368536107/40000000000 : ℝ) (992106701337/1000000000000 : ℝ) (496053350669/500000000000 : ℝ) (992075300909/1000000000000 : ℝ) (99207530091/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 1 (992106701337/1000000000000 : ℝ) (496053350669/500000000000 : ℝ) (992075300909/1000000000000 : ℝ) (99207530091/100000000000 : ℝ) (992091001123/1000000000000 : ℝ) (248022750281/250000000000 : ℝ) (496045500499/500000000000 : ℝ) (992091001/1000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 2 (992091001123/1000000000000 : ℝ) (248022750281/250000000000 : ℝ) (496045500499/500000000000 : ℝ) (992091001/1000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 3 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 4 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 5 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 6 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33371/262144 : ℝ)) 7 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33371/262144 : ℝ))) (11061613311/62500000000 : ℝ) (88492906491/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11061613311/62500000000 : ℝ) (88492906491/500000000000 : ℝ) (73561613311/125000000000 : ℝ) (588492906491/1000000000000 : ℝ) (420696818357/1000000000000 : ℝ) (84139363673/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 1 (73561613311/125000000000 : ℝ) (588492906491/1000000000000 : ℝ) (420696818357/1000000000000 : ℝ) (84139363673/200000000000 : ℝ) (252297431211/500000000000 : ℝ) (126148715607/250000000000 : ℝ) (497571194287/1000000000000 : ℝ) (248785597147/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 2 (252297431211/500000000000 : ℝ) (126148715607/250000000000 : ℝ) (497571194287/1000000000000 : ℝ) (248785597147/500000000000 : ℝ) (250541514177/500000000000 : ℝ) (501083028361/1000000000000 : ℝ) (501070721881/1000000000000 : ℝ) (15658460059/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 3 (250541514177/500000000000 : ℝ) (501083028361/1000000000000 : ℝ) (501070721881/1000000000000 : ℝ) (15658460059/31250000000 : ℝ) (501076875117/1000000000000 : ℝ) (4008615001/8000000000 : ℝ) (501076875079/1000000000000 : ℝ) (501076875087/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 4 (501076875117/1000000000000 : ℝ) (4008615001/8000000000 : ℝ) (501076875079/1000000000000 : ℝ) (501076875087/1000000000000 : ℝ) (250538437549/500000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 5 (250538437549/500000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 6 (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33371/262144 : ℝ))) 7 (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33371/262144 : ℝ)) hmem 8 (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33371/262144 : ℝ))) hcmem 8 (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33371/262144 : ℝ)) (49604550053/50000000000 : ℝ) (496045500531/500000000000 : ℝ) (501076875097/1000000000000 : ℝ) (250538437553/500000000000 : ℝ) (99170554163/125000000000 : ℝ) (793364433321/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0669_exp_lower
  have heNumeric : (2054902256153/1000000000000 : ℝ)/4 ≤ Real.exp (-85256458011963/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902256153/1000000000000 : ℝ)/4 ≤ Real.exp ((66741/524288 : ℝ)-(793364433321/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66741/524288 : ℝ) (33371/262144 : ℝ) (793364433321/1000000000000 : ℝ) (2054902256153/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0670; no trusted numerical premise.
theorem cover8_leaf0670_exp_radius : (998012880538135683/1000000000000000000 : ℝ) ≤ Real.exp ((-66743/4194304 : ℝ)/8) ∧ Real.exp ((-66743/4194304 : ℝ)/8) ≤ (249503220134533921/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66743/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0670_exp_lower : (460056743902007223/500000000000000000 : ℝ) ≤ Real.exp ((-42628229241909/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628229241909/64000000000000 : ℝ)/8) ≤ (920113487804014447/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628229241909/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0670_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451124289/500000000000 : ℝ) ≤ 4*Real.exp (33371/262144 : ℝ)*Real.exp (-mu (radius 8 (66743/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451124289/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66743/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0670_exp_radius
  have hrNumeric : (49210658401/50000000000 : ℝ) ≤ Real.exp (-66743/4194304 : ℝ) ∧ Real.exp (-66743/4194304 : ℝ) ≤ (984213168021/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49210658401/50000000000 : ℝ) ≤ (radius 8 (66743/524288 : ℝ)) ∧ (radius 8 (66743/524288 : ℝ)) ≤ (984213168021/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66743/524288 : ℝ)) (49210658401/50000000000 : ℝ) (984213168021/1000000000000 : ℝ) (44246779469/250000000000 : ℝ) (88493558941/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66743/524288 : ℝ)) (49210658401/50000000000 : ℝ) (984213168021/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49210658401/50000000000 : ℝ) (984213168021/1000000000000 : ℝ) (99210658401/100000000000 : ℝ) (992106584011/1000000000000 : ℝ) (248018795661/250000000000 : ℝ) (496037591323/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 1 (99210658401/100000000000 : ℝ) (992106584011/1000000000000 : ℝ) (248018795661/250000000000 : ℝ) (496037591323/500000000000 : ℝ) (992090883327/1000000000000 : ℝ) (992090883329/1000000000000 : ℝ) (496045441601/500000000000 : ℝ) (198418176641/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 2 (992090883327/1000000000000 : ℝ) (992090883329/1000000000000 : ℝ) (496045441601/500000000000 : ℝ) (198418176641/200000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 3 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 4 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 5 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 6 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66743/524288 : ℝ)) 7 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66743/524288 : ℝ))) (44246779469/250000000000 : ℝ) (88493558941/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44246779469/250000000000 : ℝ) (88493558941/500000000000 : ℝ) (294246779469/500000000000 : ℝ) (588493558941/1000000000000 : ℝ) (420698369233/1000000000000 : ℝ) (420698369241/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 1 (294246779469/500000000000 : ℝ) (588493558941/1000000000000 : ℝ) (420698369233/1000000000000 : ℝ) (420698369241/1000000000000 : ℝ) (100919192817/200000000000 : ℝ) (504595964091/1000000000000 : ℝ) (99514477449/200000000000 : ℝ) (124393096813/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 2 (100919192817/200000000000 : ℝ) (504595964091/1000000000000 : ℝ) (99514477449/200000000000 : ℝ) (124393096813/250000000000 : ℝ) (100216835133/200000000000 : ℝ) (62635521959/125000000000 : ℝ) (501071869539/1000000000000 : ℝ) (501071869547/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 3 (100216835133/200000000000 : ℝ) (62635521959/125000000000 : ℝ) (501071869539/1000000000000 : ℝ) (501071869547/1000000000000 : ℝ) (250539011301/500000000000 : ℝ) (50107802261/100000000000 : ℝ) (125269505641/250000000000 : ℝ) (125269505643/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 4 (250539011301/500000000000 : ℝ) (50107802261/100000000000 : ℝ) (125269505641/250000000000 : ℝ) (125269505643/250000000000 : ℝ) (501078022583/1000000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 5 (501078022583/1000000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 6 (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66743/524288 : ℝ))) 7 (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66743/524288 : ℝ)) hmem 8 (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66743/524288 : ℝ))) hcmem 8 (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66743/524288 : ℝ)) (15501420051/15625000000 : ℝ) (992090883267/1000000000000 : ℝ) (250539011291/500000000000 : ℝ) (501078022591/1000000000000 : ℝ) (396683172169/500000000000 : ℝ) (198341586089/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0670_exp_lower
  have heNumeric : (1027451124289/500000000000 : ℝ)/4 ≤ Real.exp (-42628229241909/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451124289/500000000000 : ℝ)/4 ≤ Real.exp ((33371/262144 : ℝ)-(198341586089/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33371/262144 : ℝ) (66743/524288 : ℝ) (198341586089/250000000000 : ℝ) (1027451124289/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0671; no trusted numerical premise.
theorem cover8_leaf0671_exp_radius : (499006425397517257/500000000000000000 : ℝ) ≤ Real.exp ((-8343/524288 : ℝ)/8) ∧ Real.exp ((-8343/524288 : ℝ)/8) ≤ (199602570159006903/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8343/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0671_exp_lower : (184022697476282019/200000000000000000 : ℝ) ≤ Real.exp ((-85256458954137/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256458954137/128000000000000 : ℝ)/8) ≤ (57507092961338131/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256458954137/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0671_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902241027/1000000000000 : ℝ) ≤ 4*Real.exp (66743/524288 : ℝ)*Real.exp (-mu (radius 8 (8343/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902241027/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8343/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0671_exp_radius
  have hrNumeric : (196842586673/200000000000 : ℝ) ≤ Real.exp (-8343/524288 : ℝ) ∧ Real.exp (-8343/524288 : ℝ) ≤ (492106466683/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196842586673/200000000000 : ℝ) ≤ (radius 8 (8343/65536 : ℝ)) ∧ (radius 8 (8343/65536 : ℝ)) ≤ (492106466683/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8343/65536 : ℝ)) (196842586673/200000000000 : ℝ) (492106466683/500000000000 : ℝ) (176988422771/1000000000000 : ℝ) (176988422777/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8343/65536 : ℝ)) (196842586673/200000000000 : ℝ) (492106466683/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196842586673/200000000000 : ℝ) (492106466683/500000000000 : ℝ) (496053233341/500000000000 : ℝ) (992106466683/1000000000000 : ℝ) (49603753219/50000000000 : ℝ) (992075064381/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 1 (496053233341/500000000000 : ℝ) (992106466683/1000000000000 : ℝ) (49603753219/50000000000 : ℝ) (992075064381/1000000000000 : ℝ) (992090765531/1000000000000 : ℝ) (248022691383/250000000000 : ℝ) (496045382703/500000000000 : ℝ) (31002836419/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 2 (992090765531/1000000000000 : ℝ) (248022691383/250000000000 : ℝ) (496045382703/500000000000 : ℝ) (31002836419/31250000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 3 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 4 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 5 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 6 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8343/65536 : ℝ)) 7 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8343/65536 : ℝ))) (176988422771/1000000000000 : ℝ) (176988422777/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176988422771/1000000000000 : ℝ) (176988422777/1000000000000 : ℝ) (117698842277/200000000000 : ℝ) (588494211389/1000000000000 : ℝ) (210349960049/500000000000 : ℝ) (210349960053/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 1 (117698842277/200000000000 : ℝ) (588494211389/1000000000000 : ℝ) (210349960049/500000000000 : ℝ) (210349960053/500000000000 : ℝ) (504597065741/1000000000000 : ℝ) (126149266437/250000000000 : ℝ) (248786790097/500000000000 : ℝ) (248786790101/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 2 (504597065741/1000000000000 : ℝ) (126149266437/250000000000 : ℝ) (248786790097/500000000000 : ℝ) (248786790101/500000000000 : ℝ) (501085322967/1000000000000 : ℝ) (20043412919/40000000000 : ℝ) (50107301719/100000000000 : ℝ) (250536508599/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 3 (501085322967/1000000000000 : ℝ) (20043412919/40000000000 : ℝ) (50107301719/100000000000 : ℝ) (250536508599/500000000000 : ℝ) (250539585039/500000000000 : ℝ) (501079170087/1000000000000 : ℝ) (12526979251/25000000000 : ℝ) (501079170049/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 4 (250539585039/500000000000 : ℝ) (501079170087/1000000000000 : ℝ) (12526979251/25000000000 : ℝ) (501079170049/1000000000000 : ℝ) (501079170059/1000000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 5 (501079170059/1000000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 6 (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8343/65536 : ℝ))) 7 (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8343/65536 : ℝ)) hmem 8 (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8343/65536 : ℝ))) hcmem 8 (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8343/65536 : ℝ)) (248022691367/250000000000 : ℝ) (99209076547/100000000000 : ℝ) (250539585029/500000000000 : ℝ) (125269792517/250000000000 : ℝ) (1239637899/1562500000 : ℝ) (793368255379/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0671_exp_lower
  have heNumeric : (2054902241027/1000000000000 : ℝ)/4 ≤ Real.exp (-85256458954137/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902241027/1000000000000 : ℝ)/4 ≤ Real.exp ((66743/524288 : ℝ)-(793368255379/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66743/524288 : ℝ) (8343/65536 : ℝ) (793368255379/1000000000000 : ℝ) (2054902241027/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0672; no trusted numerical premise.
theorem cover8_leaf0672_exp_radius : (99801282105193423/100000000000000000 : ℝ) ≤ Real.exp ((-66745/4194304 : ℝ)/8) ∧ Real.exp ((-66745/4194304 : ℝ)/8) ≤ (998012821051934231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66745/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0672_exp_lower : (184022697392152197/200000000000000000 : ℝ) ≤ Real.exp ((-2131411485557/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131411485557/3200000000000 : ℝ)/8) ≤ (460056743480380493/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131411485557/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0672_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862779189/125000000000 : ℝ) ≤ 4*Real.exp (8343/65536 : ℝ)*Real.exp (-mu (radius 8 (66745/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862779189/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66745/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0672_exp_radius
  have hrNumeric : (98421269871/100000000000 : ℝ) ≤ Real.exp (-66745/4194304 : ℝ) ∧ Real.exp (-66745/4194304 : ℝ) ≤ (984212698711/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98421269871/100000000000 : ℝ) ≤ (radius 8 (66745/524288 : ℝ)) ∧ (radius 8 (66745/524288 : ℝ)) ≤ (984212698711/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66745/524288 : ℝ)) (98421269871/100000000000 : ℝ) (984212698711/1000000000000 : ℝ) (22123715957/125000000000 : ℝ) (176989727663/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66745/524288 : ℝ)) (98421269871/100000000000 : ℝ) (984212698711/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98421269871/100000000000 : ℝ) (984212698711/1000000000000 : ℝ) (198421269871/200000000000 : ℝ) (248026587339/250000000000 : ℝ) (198414989223/200000000000 : ℝ) (248018736529/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 1 (198421269871/200000000000 : ℝ) (248026587339/250000000000 : ℝ) (198414989223/200000000000 : ℝ) (248018736529/250000000000 : ℝ) (198418129547/200000000000 : ℝ) (124011330967/125000000000 : ℝ) (99209064761/100000000000 : ℝ) (248022661903/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 2 (198418129547/200000000000 : ℝ) (124011330967/125000000000 : ℝ) (99209064761/100000000000 : ℝ) (248022661903/250000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 3 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 4 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 5 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 6 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66745/524288 : ℝ)) 7 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66745/524288 : ℝ))) (22123715957/125000000000 : ℝ) (176989727663/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22123715957/125000000000 : ℝ) (176989727663/1000000000000 : ℝ) (147123715957/250000000000 : ℝ) (73561857979/125000000000 : ℝ) (84140294189/200000000000 : ℝ) (84140294191/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 1 (147123715957/250000000000 : ℝ) (73561857979/125000000000 : ℝ) (84140294189/200000000000 : ℝ) (84140294191/200000000000 : ℝ) (252299083693/500000000000 : ℝ) (252299083697/500000000000 : ℝ) (49757477313/100000000000 : ℝ) (497574773139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 2 (252299083693/500000000000 : ℝ) (252299083697/500000000000 : ℝ) (49757477313/100000000000 : ℝ) (497574773139/1000000000000 : ℝ) (250543235129/500000000000 : ℝ) (501086470267/1000000000000 : ℝ) (125268541207/250000000000 : ℝ) (250537082419/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 3 (250543235129/500000000000 : ℝ) (501086470267/1000000000000 : ℝ) (125268541207/250000000000 : ℝ) (250537082419/500000000000 : ℝ) (501080317543/1000000000000 : ℝ) (501080317553/1000000000000 : ℝ) (100216063501/200000000000 : ℝ) (100216063503/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 4 (501080317543/1000000000000 : ℝ) (501080317553/1000000000000 : ℝ) (100216063501/200000000000 : ℝ) (100216063503/200000000000 : ℝ) (125270079381/250000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 5 (125270079381/250000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 6 (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66745/524288 : ℝ))) 7 (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66745/524288 : ℝ)) hmem 8 (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66745/524288 : ℝ))) hcmem 8 (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66745/524288 : ℝ)) (124011330959/125000000000 : ℝ) (496045323837/500000000000 : ℝ) (501080317523/1000000000000 : ℝ) (250540158767/500000000000 : ℝ) (158674033273/200000000000 : ℝ) (158674033277/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0672_exp_lower
  have heNumeric : (256862779189/125000000000 : ℝ)/4 ≤ Real.exp (-2131411485557/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862779189/125000000000 : ℝ)/4 ≤ Real.exp ((8343/65536 : ℝ)-(158674033277/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8343/65536 : ℝ) (66745/524288 : ℝ) (158674033277/200000000000 : ℝ) (256862779189/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0673; no trusted numerical premise.
theorem cover8_leaf0673_exp_radius : (998012791308834833/1000000000000000000 : ℝ) ≤ Real.exp ((-33373/2097152 : ℝ)/8) ∧ Real.exp ((-33373/2097152 : ℝ)/8) ≤ (499006395654417417/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33373/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0673_exp_lower : (460056743271781151/500000000000000000 : ℝ) ≤ Real.exp ((-85256459886583/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256459886583/128000000000000 : ℝ)/8) ≤ (920113486543562303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256459886583/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0673_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451113029/500000000000 : ℝ) ≤ 4*Real.exp (66745/524288 : ℝ)*Real.exp (-mu (radius 8 (33373/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451113029/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33373/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0673_exp_radius
  have hrNumeric : (123026558007/125000000000 : ℝ) ≤ Real.exp (-33373/2097152 : ℝ) ∧ Real.exp (-33373/2097152 : ℝ) ≤ (984212464057/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123026558007/125000000000 : ℝ) ≤ (radius 8 (33373/262144 : ℝ)) ∧ (radius 8 (33373/262144 : ℝ)) ≤ (984212464057/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33373/262144 : ℝ)) (123026558007/125000000000 : ℝ) (984212464057/1000000000000 : ℝ) (88495516263/500000000000 : ℝ) (176991032533/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33373/262144 : ℝ)) (123026558007/125000000000 : ℝ) (984212464057/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123026558007/125000000000 : ℝ) (984212464057/1000000000000 : ℝ) (248026558007/250000000000 : ℝ) (992106232029/1000000000000 : ℝ) (992074827851/1000000000000 : ℝ) (248018706963/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 1 (248026558007/250000000000 : ℝ) (992106232029/1000000000000 : ℝ) (992074827851/1000000000000 : ℝ) (248018706963/250000000000 : ℝ) (992090529939/1000000000000 : ℝ) (992090529941/1000000000000 : ℝ) (198418105963/200000000000 : ℝ) (992090529817/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 2 (992090529939/1000000000000 : ℝ) (992090529941/1000000000000 : ℝ) (198418105963/200000000000 : ℝ) (992090529817/1000000000000 : ℝ) (992090529877/1000000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 3 (992090529877/1000000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 4 (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 5 (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 6 (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33373/262144 : ℝ)) 7 (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33373/262144 : ℝ))) (88495516263/500000000000 : ℝ) (176991032533/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88495516263/500000000000 : ℝ) (176991032533/1000000000000 : ℝ) (588495516263/1000000000000 : ℝ) (588495516267/1000000000000 : ℝ) (420703021769/1000000000000 : ℝ) (210351510889/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 1 (588495516263/1000000000000 : ℝ) (588495516267/1000000000000 : ℝ) (420703021769/1000000000000 : ℝ) (210351510889/500000000000 : ℝ) (63074908627/125000000000 : ℝ) (504599269023/1000000000000 : ℝ) (15549248939/31250000000 : ℝ) (62196995757/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 2 (63074908627/125000000000 : ℝ) (504599269023/1000000000000 : ℝ) (15549248939/31250000000 : ℝ) (62196995757/125000000000 : ℝ) (125271904383/250000000000 : ℝ) (25054380877/50000000000 : ℝ) (10021506249/20000000000 : ℝ) (501075312459/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 3 (125271904383/250000000000 : ℝ) (25054380877/50000000000 : ℝ) (10021506249/20000000000 : ℝ) (501075312459/1000000000000 : ℝ) (501081464991/1000000000000 : ℝ) (100216293/200000000 : ℝ) (501081464953/1000000000000 : ℝ) (250540732481/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 4 (501081464991/1000000000000 : ℝ) (100216293/200000000 : ℝ) (501081464953/1000000000000 : ℝ) (250540732481/500000000000 : ℝ) (125270366243/250000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 5 (125270366243/250000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 6 (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33373/262144 : ℝ))) 7 (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33373/262144 : ℝ)) hmem 8 (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33373/262144 : ℝ))) hcmem 8 (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33373/262144 : ℝ)) (248022632469/250000000000 : ℝ) (992090529879/1000000000000 : ℝ) (501081464971/1000000000000 : ℝ) (501081464981/1000000000000 : ℝ) (396686038671/500000000000 : ℝ) (793372077361/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0673_exp_lower
  have heNumeric : (1027451113029/500000000000 : ℝ)/4 ≤ Real.exp (-85256459886583/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451113029/500000000000 : ℝ)/4 ≤ Real.exp ((66745/524288 : ℝ)-(793372077361/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66745/524288 : ℝ) (33373/262144 : ℝ) (793372077361/1000000000000 : ℝ) (1027451113029/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0674; no trusted numerical premise.
theorem cover8_leaf0674_exp_radius : (998012761565736323/1000000000000000000 : ℝ) ≤ Real.exp ((-66747/4194304 : ℝ)/8) ∧ Real.exp ((-66747/4194304 : ℝ)/8) ≤ (249503190391434081/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66747/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0674_exp_lower : (230028371531935947/250000000000000000 : ℝ) ≤ Real.exp ((-1705129206987/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705129206987/2560000000000 : ℝ)/8) ≤ (920113486127743789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705129206987/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0674_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902218629/1000000000000 : ℝ) ≤ 4*Real.exp (33373/262144 : ℝ)*Real.exp (-mu (radius 8 (66747/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902218629/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66747/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0674_exp_radius
  have hrNumeric : (984212229401/1000000000000 : ℝ) ≤ Real.exp (-66747/4194304 : ℝ) ∧ Real.exp (-66747/4194304 : ℝ) ≤ (492106114701/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984212229401/1000000000000 : ℝ) ≤ (radius 8 (66747/524288 : ℝ)) ∧ (radius 8 (66747/524288 : ℝ)) ≤ (492106114701/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66747/524288 : ℝ)) (984212229401/1000000000000 : ℝ) (492106114701/500000000000 : ℝ) (11062021087/62500000000 : ℝ) (88496168699/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66747/524288 : ℝ)) (984212229401/1000000000000 : ℝ) (492106114701/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984212229401/1000000000000 : ℝ) (492106114701/500000000000 : ℝ) (9921061147/10000000000 : ℝ) (992106114701/1000000000000 : ℝ) (496037354793/500000000000 : ℝ) (992074709587/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 1 (9921061147/10000000000 : ℝ) (992106114701/1000000000000 : ℝ) (496037354793/500000000000 : ℝ) (992074709587/1000000000000 : ℝ) (992090412143/1000000000000 : ℝ) (62005650759/62500000000 : ℝ) (496045206009/500000000000 : ℝ) (49604520601/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 2 (992090412143/1000000000000 : ℝ) (62005650759/62500000000 : ℝ) (496045206009/500000000000 : ℝ) (49604520601/50000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 3 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 4 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 5 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 6 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66747/524288 : ℝ)) 7 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66747/524288 : ℝ))) (11062021087/62500000000 : ℝ) (88496168699/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11062021087/62500000000 : ℝ) (88496168699/500000000000 : ℝ) (73562021087/125000000000 : ℝ) (588496168699/1000000000000 : ℝ) (210352286291/500000000000 : ℝ) (42070457259/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 1 (73562021087/125000000000 : ℝ) (588496168699/1000000000000 : ℝ) (210352286291/500000000000 : ℝ) (42070457259/100000000000 : ℝ) (504600370639/1000000000000 : ℝ) (100920074129/200000000000 : ℝ) (248788579479/500000000000 : ℝ) (99515431793/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 2 (504600370639/1000000000000 : ℝ) (100920074129/200000000000 : ℝ) (248788579479/500000000000 : ℝ) (99515431793/200000000000 : ℝ) (250544382399/500000000000 : ℝ) (100217752961/200000000000 : ℝ) (100215292013/200000000000 : ℝ) (62634557509/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 3 (250544382399/500000000000 : ℝ) (100217752961/200000000000 : ℝ) (100215292013/200000000000 : ℝ) (62634557509/125000000000 : ℝ) (501082612431/1000000000000 : ℝ) (501082612439/1000000000000 : ℝ) (501082612393/1000000000000 : ℝ) (501082612401/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 4 (501082612431/1000000000000 : ℝ) (501082612439/1000000000000 : ℝ) (501082612393/1000000000000 : ℝ) (501082612401/1000000000000 : ℝ) (125270653103/250000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 5 (125270653103/250000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 6 (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66747/524288 : ℝ))) 7 (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66747/524288 : ℝ)) hmem 8 (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66747/524288 : ℝ))) hcmem 8 (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66747/524288 : ℝ)) (12401130151/12500000000 : ℝ) (496045206041/500000000000 : ℝ) (501082612411/1000000000000 : ℝ) (25054130621/50000000000 : ℝ) (198343497077/250000000000 : ℝ) (31734959533/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0674_exp_lower
  have heNumeric : (2054902218629/1000000000000 : ℝ)/4 ≤ Real.exp (-1705129206987/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902218629/1000000000000 : ℝ)/4 ≤ Real.exp ((33373/262144 : ℝ)-(31734959533/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33373/262144 : ℝ) (66747/524288 : ℝ) (31734959533/40000000000 : ℝ) (2054902218629/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0650_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0650_certificate
#check SmaleRate.Proofs.cover8_leaf0651_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0651_certificate
#check SmaleRate.Proofs.cover8_leaf0652_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0652_certificate
#check SmaleRate.Proofs.cover8_leaf0653_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0653_certificate
#check SmaleRate.Proofs.cover8_leaf0654_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0654_certificate
#check SmaleRate.Proofs.cover8_leaf0655_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0655_certificate
#check SmaleRate.Proofs.cover8_leaf0656_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0656_certificate
#check SmaleRate.Proofs.cover8_leaf0657_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0657_certificate
#check SmaleRate.Proofs.cover8_leaf0658_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0658_certificate
#check SmaleRate.Proofs.cover8_leaf0659_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0659_certificate
#check SmaleRate.Proofs.cover8_leaf0660_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0660_certificate
#check SmaleRate.Proofs.cover8_leaf0661_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0661_certificate
#check SmaleRate.Proofs.cover8_leaf0662_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0662_certificate
#check SmaleRate.Proofs.cover8_leaf0663_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0663_certificate
#check SmaleRate.Proofs.cover8_leaf0664_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0664_certificate
#check SmaleRate.Proofs.cover8_leaf0665_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0665_certificate
#check SmaleRate.Proofs.cover8_leaf0666_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0666_certificate
#check SmaleRate.Proofs.cover8_leaf0667_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0667_certificate
#check SmaleRate.Proofs.cover8_leaf0668_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0668_certificate
#check SmaleRate.Proofs.cover8_leaf0669_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0669_certificate
#check SmaleRate.Proofs.cover8_leaf0670_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0670_certificate
#check SmaleRate.Proofs.cover8_leaf0671_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0671_certificate
#check SmaleRate.Proofs.cover8_leaf0672_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0672_certificate
#check SmaleRate.Proofs.cover8_leaf0673_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0673_certificate
#check SmaleRate.Proofs.cover8_leaf0674_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0674_certificate
