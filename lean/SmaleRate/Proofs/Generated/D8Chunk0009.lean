/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0225; no trusted numerical premise.
theorem cover8_leaf0225_exp_radius : (499020345362804869/500000000000000000 : ℝ) ≤ Real.exp ((-4113/262144 : ℝ)/8) ∧ Real.exp ((-4113/262144 : ℝ)/8) ≤ (998040690725609739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4113/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0225_exp_lower : (460057105158223537/500000000000000000 : ℝ) ≤ Real.exp ((-21313913598893/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313913598893/32000000000000 : ℝ)/8) ≤ (36804568412657883/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313913598893/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0225_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491515739/100000000000 : ℝ) ≤ 4*Real.exp (16451/131072 : ℝ)*Real.exp (-mu (radius 8 (4113/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205491515739/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4113/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0225_exp_radius
  have hrNumeric : (7875460757/8000000000 : ℝ) ≤ Real.exp (-4113/262144 : ℝ) ∧ Real.exp (-4113/262144 : ℝ) ≤ (492216297313/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7875460757/8000000000 : ℝ) ≤ (radius 8 (4113/32768 : ℝ)) ∧ (radius 8 (4113/32768 : ℝ)) ≤ (492216297313/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4113/32768 : ℝ)) (7875460757/8000000000 : ℝ) (492216297313/500000000000 : ℝ) (87881264553/500000000000 : ℝ) (175762529113/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4113/32768 : ℝ)) (7875460757/8000000000 : ℝ) (492216297313/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7875460757/8000000000 : ℝ) (492216297313/500000000000 : ℝ) (31006759291/31250000000 : ℝ) (992216297313/1000000000000 : ℝ) (992185766187/1000000000000 : ℝ) (248046441547/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 1 (31006759291/31250000000 : ℝ) (992216297313/1000000000000 : ℝ) (992185766187/1000000000000 : ℝ) (248046441547/250000000000 : ℝ) (992201031749/1000000000000 : ℝ) (992201031751/1000000000000 : ℝ) (62012564477/62500000000 : ℝ) (496100515817/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 2 (992201031749/1000000000000 : ℝ) (992201031751/1000000000000 : ℝ) (62012564477/62500000000 : ℝ) (496100515817/500000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 3 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 4 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 5 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 6 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4113/32768 : ℝ)) 7 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4113/32768 : ℝ))) (87881264553/500000000000 : ℝ) (175762529113/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87881264553/500000000000 : ℝ) (175762529113/1000000000000 : ℝ) (587881264553/1000000000000 : ℝ) (587881264557/1000000000000 : ℝ) (419240419217/1000000000000 : ℝ) (419240419227/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 1 (587881264553/1000000000000 : ℝ) (587881264557/1000000000000 : ℝ) (419240419217/1000000000000 : ℝ) (419240419227/1000000000000 : ℝ) (100712168377/200000000000 : ℝ) (125890210473/250000000000 : ℝ) (99290198469/200000000000 : ℝ) (248225496177/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 2 (100712168377/200000000000 : ℝ) (125890210473/250000000000 : ℝ) (99290198469/200000000000 : ℝ) (248225496177/500000000000 : ℝ) (100001183423/200000000000 : ℝ) (500005917123/1000000000000 : ℝ) (249996639807/500000000000 : ℝ) (499993279623/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 3 (100001183423/200000000000 : ℝ) (500005917123/1000000000000 : ℝ) (249996639807/500000000000 : ℝ) (499993279623/1000000000000 : ℝ) (124999899591/250000000000 : ℝ) (499999598373/1000000000000 : ℝ) (124999899581/250000000000 : ℝ) (249999799167/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 4 (124999899591/250000000000 : ℝ) (499999598373/1000000000000 : ℝ) (124999899581/250000000000 : ℝ) (249999799167/500000000000 : ℝ) (62499949793/125000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 5 (62499949793/125000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 6 (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4113/32768 : ℝ))) 7 (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4113/32768 : ℝ)) hmem 8 (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4113/32768 : ℝ))) hcmem 8 (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4113/32768 : ℝ)) (99220103169/100000000000 : ℝ) (992201031693/1000000000000 : ℝ) (499999598343/1000000000000 : ℝ) (249999799177/500000000000 : ℝ) (791570969379/1000000000000 : ℝ) (791570969399/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0225_exp_lower
  have heNumeric : (205491515739/100000000000 : ℝ)/4 ≤ Real.exp (-21313913598893/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491515739/100000000000 : ℝ)/4 ≤ Real.exp ((16451/131072 : ℝ)-(791570969399/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16451/131072 : ℝ) (4113/32768 : ℝ) (791570969399/1000000000000 : ℝ) (205491515739/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0226; no trusted numerical premise.
theorem cover8_leaf0226_exp_radius : (199608114349979029/200000000000000000 : ℝ) ≤ Real.exp ((-16453/1048576 : ℝ)/8) ∧ Real.exp ((-16453/1048576 : ℝ)/8) ≤ (499020285874947573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16453/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0226_exp_lower : (184022840036290041/200000000000000000 : ℝ) ≤ Real.exp ((-5328479104679/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328479104679/8000000000000 : ℝ)/8) ≤ (460057100090725103/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328479104679/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0226_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864372039/125000000000 : ℝ) ≤ 4*Real.exp (4113/32768 : ℝ)*Real.exp (-mu (radius 8 (16453/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256864372039/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16453/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0226_exp_radius
  have hrNumeric : (492215827899/500000000000 : ℝ) ≤ Real.exp (-16453/1048576 : ℝ) ∧ Real.exp (-16453/1048576 : ℝ) ≤ (984431655799/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492215827899/500000000000 : ℝ) ≤ (radius 8 (16453/131072 : ℝ)) ∧ (radius 8 (16453/131072 : ℝ)) ≤ (984431655799/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16453/131072 : ℝ)) (492215827899/500000000000 : ℝ) (984431655799/1000000000000 : ℝ) (43941946831/250000000000 : ℝ) (17576778733/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16453/131072 : ℝ)) (492215827899/500000000000 : ℝ) (984431655799/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492215827899/500000000000 : ℝ) (984431655799/1000000000000 : ℝ) (992215827899/1000000000000 : ℝ) (9922158279/10000000000 : ℝ) (248046323269/250000000000 : ℝ) (496092646539/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 1 (992215827899/1000000000000 : ℝ) (9922158279/10000000000 : ℝ) (248046323269/250000000000 : ℝ) (496092646539/500000000000 : ℝ) (992200560487/1000000000000 : ℝ) (992200560489/1000000000000 : ℝ) (99220056037/100000000000 : ℝ) (248050140093/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 2 (992200560487/1000000000000 : ℝ) (992200560489/1000000000000 : ℝ) (99220056037/100000000000 : ℝ) (248050140093/250000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 3 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 4 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 5 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 6 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16453/131072 : ℝ)) 7 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16453/131072 : ℝ))) (43941946831/250000000000 : ℝ) (17576778733/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43941946831/250000000000 : ℝ) (17576778733/100000000000 : ℝ) (293941946831/500000000000 : ℝ) (117576778733/200000000000 : ℝ) (83849338059/200000000000 : ℝ) (419246690303/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 1 (293941946831/500000000000 : ℝ) (117576778733/200000000000 : ℝ) (83849338059/200000000000 : ℝ) (419246690303/1000000000000 : ℝ) (251782645989/500000000000 : ℝ) (31472830749/62500000000 : ℝ) (496455815451/1000000000000 : ℝ) (248227907729/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 2 (251782645989/500000000000 : ℝ) (31472830749/62500000000 : ℝ) (496455815451/1000000000000 : ℝ) (248227907729/500000000000 : ℝ) (250005276857/500000000000 : ℝ) (500010553721/1000000000000 : ℝ) (499997917657/1000000000000 : ℝ) (15624934927/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 3 (250005276857/500000000000 : ℝ) (500010553721/1000000000000 : ℝ) (499997917657/1000000000000 : ℝ) (15624934927/31250000000 : ℝ) (100000847137/200000000000 : ℝ) (500004235693/1000000000000 : ℝ) (100000847129/200000000000 : ℝ) (500004235653/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 4 (100000847137/200000000000 : ℝ) (500004235693/1000000000000 : ℝ) (100000847129/200000000000 : ℝ) (500004235653/1000000000000 : ℝ) (100000847133/200000000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 5 (100000847133/200000000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 6 (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16453/131072 : ℝ))) 7 (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16453/131072 : ℝ)) hmem 8 (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16453/131072 : ℝ))) hcmem 8 (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16453/131072 : ℝ)) (248050140107/250000000000 : ℝ) (992200560431/1000000000000 : ℝ) (31250264729/62500000000 : ℝ) (500004235673/1000000000000 : ℝ) (158315737379/200000000000 : ℝ) (791578686913/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0226_exp_lower
  have heNumeric : (256864372039/125000000000 : ℝ)/4 ≤ Real.exp (-5328479104679/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864372039/125000000000 : ℝ)/4 ≤ Real.exp ((4113/32768 : ℝ)-(791578686913/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4113/32768 : ℝ) (16453/131072 : ℝ) (791578686913/1000000000000 : ℝ) (256864372039/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0227; no trusted numerical premise.
theorem cover8_leaf0227_exp_radius : (62377528298387171/62500000000000000 : ℝ) ≤ Real.exp ((-8227/524288 : ℝ)/8) ∧ Real.exp ((-8227/524288 : ℝ)/8) ≤ (998040452774194737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8227/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0227_exp_lower : (920114190081762829/1000000000000000000 : ℝ) ≤ Real.exp ((-4262783845743/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262783845743/6400000000000 : ℝ)/8) ≤ (92011419008176283/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262783845743/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0227_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982959173/200000000000 : ℝ) ≤ 4*Real.exp (16453/131072 : ℝ)*Real.exp (-mu (radius 8 (8227/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410982959173/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8227/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0227_exp_radius
  have hrNumeric : (984430716971/1000000000000 : ℝ) ≤ Real.exp (-8227/524288 : ℝ) ∧ Real.exp (-8227/524288 : ℝ) ≤ (246107679243/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984430716971/1000000000000 : ℝ) ≤ (radius 8 (8227/65536 : ℝ)) ∧ (radius 8 (8227/65536 : ℝ)) ≤ (246107679243/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8227/65536 : ℝ)) (984430716971/1000000000000 : ℝ) (246107679243/250000000000 : ℝ) (175773045379/1000000000000 : ℝ) (87886522693/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8227/65536 : ℝ)) (984430716971/1000000000000 : ℝ) (246107679243/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984430716971/1000000000000 : ℝ) (246107679243/250000000000 : ℝ) (198443071697/200000000000 : ℝ) (496107679243/500000000000 : ℝ) (496092409983/500000000000 : ℝ) (992184819967/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 1 (198443071697/200000000000 : ℝ) (496107679243/500000000000 : ℝ) (496092409983/500000000000 : ℝ) (992184819967/1000000000000 : ℝ) (39688003569/40000000000 : ℝ) (992200089227/1000000000000 : ℝ) (248050022277/250000000000 : ℝ) (99220008911/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 2 (39688003569/40000000000 : ℝ) (992200089227/1000000000000 : ℝ) (248050022277/250000000000 : ℝ) (99220008911/100000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 3 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 4 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 5 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 6 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8227/65536 : ℝ)) 7 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8227/65536 : ℝ))) (175773045379/1000000000000 : ℝ) (87886522693/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175773045379/1000000000000 : ℝ) (87886522693/500000000000 : ℝ) (587886522689/1000000000000 : ℝ) (587886522693/1000000000000 : ℝ) (83850592217/200000000000 : ℝ) (209626480547/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 1 (587886522689/1000000000000 : ℝ) (587886522693/1000000000000 : ℝ) (83850592217/200000000000 : ℝ) (209626480547/500000000000 : ℝ) (503569741887/1000000000000 : ℝ) (251784870947/500000000000 : ℝ) (248230319169/500000000000 : ℝ) (248230319173/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 2 (503569741887/1000000000000 : ℝ) (251784870947/500000000000 : ℝ) (248230319169/500000000000 : ℝ) (248230319173/500000000000 : ℝ) (15625474691/31250000000 : ℝ) (12500379753/25000000000 : ℝ) (250001277749/500000000000 : ℝ) (250001277753/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 3 (15625474691/31250000000 : ℝ) (12500379753/25000000000 : ℝ) (250001277749/500000000000 : ℝ) (250001277753/500000000000 : ℝ) (100001774561/200000000000 : ℝ) (500008872813/1000000000000 : ℝ) (100001774553/200000000000 : ℝ) (250004436387/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 4 (100001774561/200000000000 : ℝ) (500008872813/1000000000000 : ℝ) (100001774553/200000000000 : ℝ) (250004436387/500000000000 : ℝ) (100001774557/200000000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 5 (100001774557/200000000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 6 (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8227/65536 : ℝ))) 7 (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8227/65536 : ℝ)) hmem 8 (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8227/65536 : ℝ))) hcmem 8 (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8227/65536 : ℝ)) (496100044583/500000000000 : ℝ) (992200089169/1000000000000 : ℝ) (31250554549/62500000000 : ℝ) (250004436397/500000000000 : ℝ) (7915864041/10000000000 : ℝ) (19789660103/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0227_exp_lower
  have heNumeric : (410982959173/200000000000 : ℝ)/4 ≤ Real.exp (-4262783845743/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982959173/200000000000 : ℝ)/4 ≤ Real.exp ((16453/131072 : ℝ)-(19789660103/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16453/131072 : ℝ) (8227/65536 : ℝ) (19789660103/25000000000 : ℝ) (410982959173/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0228; no trusted numerical premise.
theorem cover8_leaf0228_exp_radius : (998040333798508509/1000000000000000000 : ℝ) ≤ Real.exp ((-16455/1048576 : ℝ)/8) ∧ Real.exp ((-16455/1048576 : ℝ)/8) ≤ (99804033379850851/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16455/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0228_exp_lower : (184022836003799029/200000000000000000 : ℝ) ≤ Real.exp ((-10656961014221/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656961014221/16000000000000 : ℝ)/8) ≤ (460057090009497573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656961014221/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0228_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914616077/1000000000000 : ℝ) ≤ 4*Real.exp (8227/65536 : ℝ)*Real.exp (-mu (radius 8 (16455/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914616077/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16455/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0228_exp_radius
  have hrNumeric : (196885955629/200000000000 : ℝ) ≤ Real.exp (-16455/1048576 : ℝ) ∧ Real.exp (-16455/1048576 : ℝ) ≤ (492214889073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196885955629/200000000000 : ℝ) ≤ (radius 8 (16455/131072 : ℝ)) ∧ (radius 8 (16455/131072 : ℝ)) ≤ (492214889073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16455/131072 : ℝ)) (196885955629/200000000000 : ℝ) (492214889073/500000000000 : ℝ) (87889151633/500000000000 : ℝ) (175778303273/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16455/131072 : ℝ)) (196885955629/200000000000 : ℝ) (492214889073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196885955629/200000000000 : ℝ) (492214889073/500000000000 : ℝ) (62013430567/62500000000 : ℝ) (992214889073/1000000000000 : ℝ) (198436869371/200000000000 : ℝ) (124023043357/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 1 (62013430567/62500000000 : ℝ) (992214889073/1000000000000 : ℝ) (198436869371/200000000000 : ℝ) (124023043357/125000000000 : ℝ) (992199617963/1000000000000 : ℝ) (198439923593/200000000000 : ℝ) (198439923569/200000000000 : ℝ) (992199617847/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 2 (992199617963/1000000000000 : ℝ) (198439923593/200000000000 : ℝ) (198439923569/200000000000 : ℝ) (992199617847/1000000000000 : ℝ) (62012476119/62500000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 3 (62012476119/62500000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 4 (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 5 (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 6 (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16455/131072 : ℝ)) 7 (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16455/131072 : ℝ))) (87889151633/500000000000 : ℝ) (175778303273/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87889151633/500000000000 : ℝ) (175778303273/1000000000000 : ℝ) (587889151633/1000000000000 : ℝ) (587889151637/1000000000000 : ℝ) (419259231581/1000000000000 : ℝ) (41925923159/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 1 (587889151633/1000000000000 : ℝ) (587889151637/1000000000000 : ℝ) (419259231581/1000000000000 : ℝ) (41925923159/100000000000 : ℝ) (503574191607/1000000000000 : ℝ) (251787095807/500000000000 : ℝ) (248232730501/500000000000 : ℝ) (49646546101/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 2 (503574191607/1000000000000 : ℝ) (251787095807/500000000000 : ℝ) (248232730501/500000000000 : ℝ) (49646546101/100000000000 : ℝ) (3906404893/7812500000 : ℝ) (62502478289/125000000000 : ℝ) (500007193133/1000000000000 : ℝ) (500007193141/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 3 (3906404893/7812500000 : ℝ) (62502478289/125000000000 : ℝ) (500007193133/1000000000000 : ℝ) (500007193141/1000000000000 : ℝ) (250006754859/500000000000 : ℝ) (500013509727/1000000000000 : ℝ) (250006754839/500000000000 : ℝ) (500013509687/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 4 (250006754859/500000000000 : ℝ) (500013509727/1000000000000 : ℝ) (250006754839/500000000000 : ℝ) (500013509687/1000000000000 : ℝ) (250006754849/500000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 5 (250006754849/500000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 6 (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16455/131072 : ℝ))) 7 (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16455/131072 : ℝ)) hmem 8 (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16455/131072 : ℝ))) hcmem 8 (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16455/131072 : ℝ)) (992199617903/1000000000000 : ℝ) (496099808953/500000000000 : ℝ) (500013509697/1000000000000 : ℝ) (500013509707/1000000000000 : ℝ) (395797060493/500000000000 : ℝ) (395797060503/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0228_exp_lower
  have heNumeric : (2054914616077/1000000000000 : ℝ)/4 ≤ Real.exp (-10656961014221/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914616077/1000000000000 : ℝ)/4 ≤ Real.exp ((8227/65536 : ℝ)-(395797060503/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8227/65536 : ℝ) (16455/131072 : ℝ) (395797060503/500000000000 : ℝ) (2054914616077/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0229; no trusted numerical premise.
theorem cover8_leaf0229_exp_radius : (199608042964567293/200000000000000000 : ℝ) ≤ Real.exp ((-2057/131072 : ℝ)/8) ∧ Real.exp ((-2057/131072 : ℝ)/8) ≤ (499020107411418233/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2057/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0229_exp_lower : (230028542498229281/250000000000000000 : ℝ) ≤ Real.exp ((-21313924817961/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313924817961/32000000000000 : ℝ)/8) ≤ (7360913359943337/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313924817961/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0229_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982887389/200000000000 : ℝ) ≤ 4*Real.exp (16455/131072 : ℝ)*Real.exp (-mu (radius 8 (2057/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410982887389/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2057/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0229_exp_radius
  have hrNumeric : (24610720983/25000000000 : ℝ) ≤ Real.exp (-2057/131072 : ℝ) ∧ Real.exp (-2057/131072 : ℝ) ≤ (984428839321/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24610720983/25000000000 : ℝ) ≤ (radius 8 (2057/16384 : ℝ)) ∧ (radius 8 (2057/16384 : ℝ)) ≤ (984428839321/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2057/16384 : ℝ)) (24610720983/25000000000 : ℝ) (984428839321/1000000000000 : ℝ) (87891780493/500000000000 : ℝ) (175783560993/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2057/16384 : ℝ)) (24610720983/25000000000 : ℝ) (984428839321/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24610720983/25000000000 : ℝ) (984428839321/1000000000000 : ℝ) (49610720983/50000000000 : ℝ) (992214419661/1000000000000 : ℝ) (198436774749/200000000000 : ℝ) (496091936873/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 1 (49610720983/50000000000 : ℝ) (992214419661/1000000000000 : ℝ) (198436774749/200000000000 : ℝ) (496091936873/500000000000 : ℝ) (496099573351/500000000000 : ℝ) (62012446669/62500000000 : ℝ) (124024893323/125000000000 : ℝ) (496099573293/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 2 (496099573351/500000000000 : ℝ) (62012446669/62500000000 : ℝ) (124024893323/125000000000 : ℝ) (496099573293/500000000000 : ℝ) (992199146643/1000000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 3 (992199146643/1000000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 4 (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 5 (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 6 (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2057/16384 : ℝ)) 7 (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2057/16384 : ℝ))) (87891780493/500000000000 : ℝ) (175783560993/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87891780493/500000000000 : ℝ) (175783560993/1000000000000 : ℝ) (587891780493/1000000000000 : ℝ) (587891780497/1000000000000 : ℝ) (419265501783/1000000000000 : ℝ) (419265501793/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 1 (587891780493/1000000000000 : ℝ) (587891780497/1000000000000 : ℝ) (419265501783/1000000000000 : ℝ) (419265501793/1000000000000 : ℝ) (251789320569/500000000000 : ℝ) (100715728229/200000000000 : ℝ) (496470283443/1000000000000 : ℝ) (124117570863/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 2 (251789320569/500000000000 : ℝ) (100715728229/200000000000 : ℝ) (496470283443/1000000000000 : ℝ) (124117570863/250000000000 : ℝ) (50002446229/100000000000 : ℝ) (500024462299/1000000000000 : ℝ) (500011830561/1000000000000 : ℝ) (50001183057/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 3 (50002446229/100000000000 : ℝ) (500024462299/1000000000000 : ℝ) (500011830561/1000000000000 : ℝ) (50001183057/100000000000 : ℝ) (20000725857/40000000000 : ℝ) (100003629287/200000000000 : ℝ) (100003629277/200000000000 : ℝ) (100003629279/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 4 (20000725857/40000000000 : ℝ) (100003629287/200000000000 : ℝ) (100003629277/200000000000 : ℝ) (100003629279/200000000000 : ℝ) (100003629281/200000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 5 (100003629281/200000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 6 (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2057/16384 : ℝ))) 7 (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2057/16384 : ℝ)) hmem 8 (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2057/16384 : ℝ))) hcmem 8 (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2057/16384 : ℝ)) (496099573321/500000000000 : ℝ) (198439829329/200000000000 : ℝ) (125004536601/250000000000 : ℝ) (100003629283/200000000000 : ℝ) (49475114847/62500000000 : ℝ) (791601837573/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0229_exp_lower
  have heNumeric : (410982887389/200000000000 : ℝ)/4 ≤ Real.exp (-21313924817961/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982887389/200000000000 : ℝ)/4 ≤ Real.exp ((16455/131072 : ℝ)-(791601837573/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16455/131072 : ℝ) (2057/16384 : ℝ) (791601837573/1000000000000 : ℝ) (410982887389/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0230; no trusted numerical premise.
theorem cover8_leaf0230_exp_radius : (199608019169435721/200000000000000000 : ℝ) ≤ Real.exp ((-16457/1048576 : ℝ)/8) ∧ Real.exp ((-16457/1048576 : ℝ)/8) ≤ (499020047923589303/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16457/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0230_exp_lower : (57507135000242113/62500000000000000 : ℝ) ≤ Real.exp ((-2664240949647/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664240949647/4000000000000 : ℝ)/8) ≤ (920114160003873809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664240949647/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0230_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196570339/40000000000 : ℝ) ≤ 4*Real.exp (2057/16384 : ℝ)*Real.exp (-mu (radius 8 (16457/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (82196570339/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16457/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0230_exp_radius
  have hrNumeric : (61526743781/62500000000 : ℝ) ≤ Real.exp (-16457/1048576 : ℝ) ∧ Real.exp (-16457/1048576 : ℝ) ≤ (984427900497/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61526743781/62500000000 : ℝ) ≤ (radius 8 (16457/131072 : ℝ)) ∧ (radius 8 (16457/131072 : ℝ)) ≤ (984427900497/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16457/131072 : ℝ)) (61526743781/62500000000 : ℝ) (984427900497/1000000000000 : ℝ) (87894409269/500000000000 : ℝ) (10986801159/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16457/131072 : ℝ)) (61526743781/62500000000 : ℝ) (984427900497/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61526743781/62500000000 : ℝ) (984427900497/1000000000000 : ℝ) (124026743781/125000000000 : ℝ) (992213950249/1000000000000 : ℝ) (198436680127/200000000000 : ℝ) (248045850159/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 1 (124026743781/125000000000 : ℝ) (992213950249/1000000000000 : ℝ) (198436680127/200000000000 : ℝ) (248045850159/250000000000 : ℝ) (992198675441/1000000000000 : ℝ) (992198675443/1000000000000 : ℝ) (992198675323/1000000000000 : ℝ) (39687947013/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 2 (992198675441/1000000000000 : ℝ) (992198675443/1000000000000 : ℝ) (992198675323/1000000000000 : ℝ) (39687947013/40000000000 : ℝ) (496099337691/500000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 3 (496099337691/500000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 4 (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 5 (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 6 (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16457/131072 : ℝ)) 7 (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16457/131072 : ℝ))) (87894409269/500000000000 : ℝ) (10986801159/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87894409269/500000000000 : ℝ) (10986801159/62500000000 : ℝ) (587894409269/1000000000000 : ℝ) (73486801159/125000000000 : ℝ) (104817942923/250000000000 : ℝ) (4192717717/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 1 (587894409269/1000000000000 : ℝ) (73486801159/125000000000 : ℝ) (104817942923/250000000000 : ℝ) (4192717717/10000000000 : ℝ) (6294788631/12500000000 : ℝ) (251791545243/500000000000 : ℝ) (496475105661/1000000000000 : ℝ) (124118776417/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 2 (6294788631/12500000000 : ℝ) (251791545243/500000000000 : ℝ) (496475105661/1000000000000 : ℝ) (124118776417/250000000000 : ℝ) (50002909807/100000000000 : ℝ) (500029098077/1000000000000 : ℝ) (500016467783/1000000000000 : ℝ) (500016467791/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 3 (50002909807/100000000000 : ℝ) (500029098077/1000000000000 : ℝ) (500016467783/1000000000000 : ℝ) (500016467791/1000000000000 : ℝ) (250011391463/500000000000 : ℝ) (250011391467/500000000000 : ℝ) (250011391443/500000000000 : ℝ) (100004556579/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 4 (250011391463/500000000000 : ℝ) (250011391467/500000000000 : ℝ) (250011391443/500000000000 : ℝ) (100004556579/200000000000 : ℝ) (250011391453/500000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 5 (250011391453/500000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 6 (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16457/131072 : ℝ))) 7 (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16457/131072 : ℝ)) hmem 8 (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16457/131072 : ℝ))) hcmem 8 (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16457/131072 : ℝ)) (992198675381/1000000000000 : ℝ) (124024834423/125000000000 : ℝ) (100004556581/200000000000 : ℝ) (100004556583/200000000000 : ℝ) (791609553799/1000000000000 : ℝ) (395804776909/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0230_exp_lower
  have heNumeric : (82196570339/40000000000 : ℝ)/4 ≤ Real.exp (-2664240949647/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196570339/40000000000 : ℝ)/4 ≤ Real.exp ((2057/16384 : ℝ)-(395804776909/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2057/16384 : ℝ) (16457/131072 : ℝ) (395804776909/500000000000 : ℝ) (82196570339/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0231; no trusted numerical premise.
theorem cover8_leaf0231_exp_radius : (998039976871534927/1000000000000000000 : ℝ) ≤ Real.exp ((-8229/524288 : ℝ)/8) ∧ Real.exp ((-8229/524288 : ℝ)/8) ≤ (62377498554470933/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8229/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0231_exp_lower : (920114150051290123/1000000000000000000 : ℝ) ≤ Real.exp ((-21313930366247/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313930366247/32000000000000 : ℝ)/8) ≤ (230028537512822531/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313930366247/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0231_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128432130041/62500000000 : ℝ) ≤ 4*Real.exp (16457/131072 : ℝ)*Real.exp (-mu (radius 8 (8229/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128432130041/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8229/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0231_exp_radius
  have hrNumeric : (984426961673/1000000000000 : ℝ) ≤ Real.exp (-8229/524288 : ℝ) ∧ Real.exp (-8229/524288 : ℝ) ≤ (492213480837/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984426961673/1000000000000 : ℝ) ≤ (radius 8 (8229/65536 : ℝ)) ∧ (radius 8 (8229/65536 : ℝ)) ≤ (492213480837/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8229/65536 : ℝ)) (984426961673/1000000000000 : ℝ) (492213480837/500000000000 : ℝ) (87897037961/500000000000 : ℝ) (21974259491/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8229/65536 : ℝ)) (984426961673/1000000000000 : ℝ) (492213480837/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984426961673/1000000000000 : ℝ) (492213480837/500000000000 : ℝ) (248053370209/250000000000 : ℝ) (992213480837/1000000000000 : ℝ) (39687317101/40000000000 : ℝ) (496091463763/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 1 (248053370209/250000000000 : ℝ) (992213480837/1000000000000 : ℝ) (39687317101/40000000000 : ℝ) (496091463763/500000000000 : ℝ) (49609910209/50000000000 : ℝ) (496099102091/500000000000 : ℝ) (496099102031/500000000000 : ℝ) (31006193877/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 2 (49609910209/50000000000 : ℝ) (496099102091/500000000000 : ℝ) (496099102031/500000000000 : ℝ) (31006193877/31250000000 : ℝ) (992198204121/1000000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 3 (992198204121/1000000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 4 (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 5 (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 6 (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8229/65536 : ℝ)) 7 (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8229/65536 : ℝ))) (87897037961/500000000000 : ℝ) (21974259491/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87897037961/500000000000 : ℝ) (21974259491/125000000000 : ℝ) (587897037961/1000000000000 : ℝ) (146974259491/250000000000 : ℝ) (209639020653/500000000000 : ℝ) (209639020657/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 1 (587897037961/1000000000000 : ℝ) (146974259491/250000000000 : ℝ) (209639020653/500000000000 : ℝ) (209639020657/500000000000 : ℝ) (503587539633/1000000000000 : ℝ) (503587539639/1000000000000 : ℝ) (62059990957/125000000000 : ℝ) (496479927663/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 2 (503587539633/1000000000000 : ℝ) (503587539639/1000000000000 : ℝ) (62059990957/125000000000 : ℝ) (496479927663/1000000000000 : ℝ) (125008433411/250000000000 : ℝ) (500033733651/1000000000000 : ℝ) (625026381/1250000000 : ℝ) (500021104807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 3 (125008433411/250000000000 : ℝ) (500033733651/1000000000000 : ℝ) (625026381/1250000000 : ℝ) (500021104807/1000000000000 : ℝ) (250013709611/500000000000 : ℝ) (500027419229/1000000000000 : ℝ) (250013709591/500000000000 : ℝ) (50002741919/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 4 (250013709611/500000000000 : ℝ) (500027419229/1000000000000 : ℝ) (250013709591/500000000000 : ℝ) (50002741919/100000000000 : ℝ) (250013709601/500000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 5 (250013709601/500000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 6 (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8229/65536 : ℝ))) 7 (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8229/65536 : ℝ)) hmem 8 (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8229/65536 : ℝ))) hcmem 8 (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8229/65536 : ℝ)) (24804955103/25000000000 : ℝ) (992198204123/1000000000000 : ℝ) (500027419201/1000000000000 : ℝ) (50002741921/100000000000 : ℝ) (24738039679/31250000000 : ℝ) (395808634873/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0231_exp_lower
  have heNumeric : (128432130041/62500000000 : ℝ)/4 ≤ Real.exp (-21313930366247/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128432130041/62500000000 : ℝ)/4 ≤ Real.exp ((16457/131072 : ℝ)-(395808634873/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16457/131072 : ℝ) (8229/65536 : ℝ) (395808634873/500000000000 : ℝ) (128432130041/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0232; no trusted numerical premise.
theorem cover8_leaf0232_exp_radius : (124754982236988179/125000000000000000 : ℝ) ≤ Real.exp ((-16459/1048576 : ℝ)/8) ∧ Real.exp ((-16459/1048576 : ℝ)/8) ≤ (998039857895905433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16459/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0232_exp_lower : (920114140135511111/1000000000000000000 : ℝ) ≤ Real.exp ((-10656966562539/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656966562539/16000000000000 : ℝ)/8) ≤ (115014267516938889/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656966562539/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0232_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982780699/200000000000 : ℝ) ≤ 4*Real.exp (8229/65536 : ℝ)*Real.exp (-mu (radius 8 (16459/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410982780699/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16459/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0232_exp_radius
  have hrNumeric : (984426022851/1000000000000 : ℝ) ≤ Real.exp (-16459/1048576 : ℝ) ∧ Real.exp (-16459/1048576 : ℝ) ≤ (246106505713/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984426022851/1000000000000 : ℝ) ≤ (radius 8 (16459/131072 : ℝ)) ∧ (radius 8 (16459/131072 : ℝ)) ≤ (246106505713/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16459/131072 : ℝ)) (984426022851/1000000000000 : ℝ) (246106505713/250000000000 : ℝ) (87899666569/500000000000 : ℝ) (21974916643/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16459/131072 : ℝ)) (984426022851/1000000000000 : ℝ) (246106505713/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984426022851/1000000000000 : ℝ) (246106505713/250000000000 : ℝ) (39688520457/40000000000 : ℝ) (496106505713/500000000000 : ℝ) (62011403401/62500000000 : ℝ) (992182454417/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 1 (39688520457/40000000000 : ℝ) (496106505713/500000000000 : ℝ) (62011403401/62500000000 : ℝ) (992182454417/1000000000000 : ℝ) (24804943323/25000000000 : ℝ) (496098866461/500000000000 : ℝ) (496098866401/500000000000 : ℝ) (248049433201/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 2 (24804943323/25000000000 : ℝ) (496098866461/500000000000 : ℝ) (496098866401/500000000000 : ℝ) (248049433201/250000000000 : ℝ) (992197732861/1000000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 3 (992197732861/1000000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 4 (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 5 (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 6 (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16459/131072 : ℝ)) 7 (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16459/131072 : ℝ))) (87899666569/500000000000 : ℝ) (21974916643/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87899666569/500000000000 : ℝ) (21974916643/125000000000 : ℝ) (587899666569/1000000000000 : ℝ) (146974916643/250000000000 : ℝ) (419284310627/1000000000000 : ℝ) (83856862127/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 1 (587899666569/1000000000000 : ℝ) (146974916643/250000000000 : ℝ) (419284310627/1000000000000 : ℝ) (83856862127/200000000000 : ℝ) (251795994299/500000000000 : ℝ) (125897997151/250000000000 : ℝ) (124121187357/250000000000 : ℝ) (99296949887/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 2 (251795994299/500000000000 : ℝ) (125897997151/250000000000 : ℝ) (124121187357/250000000000 : ℝ) (99296949887/200000000000 : ℝ) (500038369013/1000000000000 : ℝ) (25001918451/50000000000 : ℝ) (50002574161/100000000000 : ℝ) (500025741617/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 3 (500038369013/1000000000000 : ℝ) (25001918451/50000000000 : ℝ) (50002574161/100000000000 : ℝ) (500025741617/1000000000000 : ℝ) (500032055311/1000000000000 : ℝ) (500032055319/1000000000000 : ℝ) (500032055271/1000000000000 : ℝ) (500032055279/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 4 (500032055311/1000000000000 : ℝ) (500032055319/1000000000000 : ℝ) (500032055271/1000000000000 : ℝ) (500032055279/1000000000000 : ℝ) (500032055291/1000000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 5 (500032055291/1000000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 6 (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16459/131072 : ℝ))) 7 (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16459/131072 : ℝ)) hmem 8 (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16459/131072 : ℝ))) hcmem 8 (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16459/131072 : ℝ)) (49609886643/50000000000 : ℝ) (992197732863/1000000000000 : ℝ) (50003205529/100000000000 : ℝ) (500032055299/1000000000000 : ℝ) (791624985337/1000000000000 : ℝ) (395812492677/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0232_exp_lower
  have heNumeric : (410982780699/200000000000 : ℝ)/4 ≤ Real.exp (-10656966562539/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982780699/200000000000 : ℝ)/4 ≤ Real.exp ((8229/65536 : ℝ)-(395812492677/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8229/65536 : ℝ) (16459/131072 : ℝ) (395812492677/500000000000 : ℝ) (410982780699/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0233; no trusted numerical premise.
theorem cover8_leaf0233_exp_radius : (998039738920290121/1000000000000000000 : ℝ) ≤ Real.exp ((-4115/262144 : ℝ)/8) ∧ Real.exp ((-4115/262144 : ℝ)/8) ≤ (499019869460145061/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4115/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0233_exp_lower : (230028532563846657/250000000000000000 : ℝ) ≤ Real.exp ((-21313935873989/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313935873989/32000000000000 : ℝ)/8) ≤ (920114130255386629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313935873989/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0233_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054913726971/1000000000000 : ℝ) ≤ 4*Real.exp (16459/131072 : ℝ)*Real.exp (-mu (radius 8 (4115/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054913726971/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4115/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0233_exp_radius
  have hrNumeric : (984425084029/1000000000000 : ℝ) ≤ Real.exp (-4115/262144 : ℝ) ∧ Real.exp (-4115/262144 : ℝ) ≤ (98442508403/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984425084029/1000000000000 : ℝ) ≤ (radius 8 (4115/32768 : ℝ)) ∧ (radius 8 (4115/32768 : ℝ)) ≤ (98442508403/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4115/32768 : ℝ)) (984425084029/1000000000000 : ℝ) (98442508403/100000000000 : ℝ) (175804590191/1000000000000 : ℝ) (87902295099/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4115/32768 : ℝ)) (984425084029/1000000000000 : ℝ) (98442508403/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984425084029/1000000000000 : ℝ) (98442508403/100000000000 : ℝ) (496106271007/500000000000 : ℝ) (198442508403/200000000000 : ℝ) (496090990653/500000000000 : ℝ) (992181981307/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 1 (496106271007/500000000000 : ℝ) (198442508403/200000000000 : ℝ) (496090990653/500000000000 : ℝ) (992181981307/1000000000000 : ℝ) (49609863083/50000000000 : ℝ) (992197261661/1000000000000 : ℝ) (496098630771/500000000000 : ℝ) (124024657693/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 2 (49609863083/50000000000 : ℝ) (992197261661/1000000000000 : ℝ) (496098630771/500000000000 : ℝ) (124024657693/125000000000 : ℝ) (992197261601/1000000000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 3 (992197261601/1000000000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 4 (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 5 (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 6 (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4115/32768 : ℝ)) 7 (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4115/32768 : ℝ))) (175804590191/1000000000000 : ℝ) (87902295099/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175804590191/1000000000000 : ℝ) (87902295099/500000000000 : ℝ) (117580459019/200000000000 : ℝ) (587902295099/1000000000000 : ℝ) (419290579659/1000000000000 : ℝ) (104822644917/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 1 (117580459019/200000000000 : ℝ) (587902295099/1000000000000 : ℝ) (419290579659/1000000000000 : ℝ) (104822644917/250000000000 : ℝ) (503596437377/1000000000000 : ℝ) (62949554673/125000000000 : ℝ) (496489570981/1000000000000 : ℝ) (496489570989/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 2 (503596437377/1000000000000 : ℝ) (62949554673/125000000000 : ℝ) (496489570981/1000000000000 : ℝ) (496489570989/1000000000000 : ℝ) (500043004179/1000000000000 : ℝ) (500043004187/1000000000000 : ℝ) (250015189109/500000000000 : ℝ) (250015189113/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 3 (500043004179/1000000000000 : ℝ) (500043004187/1000000000000 : ℝ) (250015189109/500000000000 : ℝ) (250015189113/500000000000 : ℝ) (250018345599/500000000000 : ℝ) (500036691207/1000000000000 : ℝ) (250018345579/500000000000 : ℝ) (500036691167/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 4 (250018345599/500000000000 : ℝ) (500036691207/1000000000000 : ℝ) (250018345579/500000000000 : ℝ) (500036691167/1000000000000 : ℝ) (250018345589/500000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 5 (250018345589/500000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 6 (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4115/32768 : ℝ))) 7 (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4115/32768 : ℝ)) hmem 8 (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4115/32768 : ℝ))) hcmem 8 (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4115/32768 : ℝ)) (1240246577/1250000000 : ℝ) (992197261603/1000000000000 : ℝ) (500036691177/1000000000000 : ℝ) (500036691187/1000000000000 : ℝ) (791632700633/1000000000000 : ℝ) (197908175163/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0233_exp_lower
  have heNumeric : (2054913726971/1000000000000 : ℝ)/4 ≤ Real.exp (-21313935873989/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054913726971/1000000000000 : ℝ)/4 ≤ Real.exp ((16459/131072 : ℝ)-(197908175163/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16459/131072 : ℝ) (4115/32768 : ℝ) (197908175163/250000000000 : ℝ) (2054913726971/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0234; no trusted numerical premise.
theorem cover8_leaf0234_exp_radius : (31188738123271531/31250000000000000 : ℝ) ≤ Real.exp ((-16461/1048576 : ℝ)/8) ∧ Real.exp ((-16461/1048576 : ℝ)/8) ≤ (998039619944688993/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16461/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0234_exp_lower : (184022824082620389/200000000000000000 : ℝ) ≤ Real.exp ((-5328484653093/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328484653093/8000000000000 : ℝ)/8) ≤ (460057060206550973/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328484653093/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0234_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456775561/500000000000 : ℝ) ≤ 4*Real.exp (4115/32768 : ℝ)*Real.exp (-mu (radius 8 (16461/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456775561/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16461/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0234_exp_radius
  have hrNumeric : (984424145209/1000000000000 : ℝ) ≤ Real.exp (-16461/1048576 : ℝ) ∧ Real.exp (-16461/1048576 : ℝ) ≤ (98442414521/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984424145209/1000000000000 : ℝ) ≤ (radius 8 (16461/131072 : ℝ)) ∧ (radius 8 (16461/131072 : ℝ)) ≤ (98442414521/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16461/131072 : ℝ)) (984424145209/1000000000000 : ℝ) (98442414521/100000000000 : ℝ) (5494057721/31250000000 : ℝ) (87904923539/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16461/131072 : ℝ)) (984424145209/1000000000000 : ℝ) (98442414521/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984424145209/1000000000000 : ℝ) (98442414521/100000000000 : ℝ) (248053018151/250000000000 : ℝ) (198442414521/200000000000 : ℝ) (992181508197/1000000000000 : ℝ) (496090754099/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 1 (248053018151/250000000000 : ℝ) (198442414521/200000000000 : ℝ) (992181508197/1000000000000 : ℝ) (496090754099/500000000000 : ℝ) (310061497/312500000 : ℝ) (496098395201/500000000000 : ℝ) (496098395141/500000000000 : ℝ) (248049197571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 2 (310061497/312500000 : ℝ) (496098395201/500000000000 : ℝ) (496098395141/500000000000 : ℝ) (248049197571/250000000000 : ℝ) (992196790341/1000000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 3 (992196790341/1000000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 4 (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 5 (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 6 (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16461/131072 : ℝ)) 7 (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16461/131072 : ℝ))) (5494057721/31250000000 : ℝ) (87904923539/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5494057721/31250000000 : ℝ) (87904923539/500000000000 : ℝ) (36744057721/62500000000 : ℝ) (587904923539/1000000000000 : ℝ) (52412106049/125000000000 : ℝ) (1048242121/2500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 1 (36744057721/62500000000 : ℝ) (587904923539/1000000000000 : ℝ) (52412106049/125000000000 : ℝ) (1048242121/2500000000 : ℝ) (125900221491/250000000000 : ℝ) (50360088597/100000000000 : ℝ) (496494392307/1000000000000 : ℝ) (248247196157/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 2 (125900221491/250000000000 : ℝ) (50360088597/100000000000 : ℝ) (496494392307/1000000000000 : ℝ) (248247196157/500000000000 : ℝ) (100009527827/200000000000 : ℝ) (250023819571/500000000000 : ℝ) (100007002923/200000000000 : ℝ) (500035014623/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 3 (100009527827/200000000000 : ℝ) (250023819571/500000000000 : ℝ) (100007002923/200000000000 : ℝ) (500035014623/1000000000000 : ℝ) (800066123/1600000000 : ℝ) (500041326883/1000000000000 : ℝ) (100008265367/200000000000 : ℝ) (500041326843/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 4 (800066123/1600000000 : ℝ) (500041326883/1000000000000 : ℝ) (100008265367/200000000000 : ℝ) (500041326843/1000000000000 : ℝ) (100008265371/200000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 5 (100008265371/200000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 6 (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16461/131072 : ℝ))) 7 (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16461/131072 : ℝ)) hmem 8 (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16461/131072 : ℝ))) hcmem 8 (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16461/131072 : ℝ)) (49609839517/50000000000 : ℝ) (992196790343/1000000000000 : ℝ) (250020663427/500000000000 : ℝ) (500041326863/1000000000000 : ℝ) (791640415603/1000000000000 : ℝ) (791640415621/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0234_exp_lower
  have heNumeric : (1027456775561/500000000000 : ℝ)/4 ≤ Real.exp (-5328484653093/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456775561/500000000000 : ℝ)/4 ≤ Real.exp ((4115/32768 : ℝ)-(791640415621/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4115/32768 : ℝ) (16461/131072 : ℝ) (791640415621/1000000000000 : ℝ) (1027456775561/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0235; no trusted numerical premise.
theorem cover8_leaf0235_exp_radius : (998039500969102047/1000000000000000000 : ℝ) ≤ Real.exp ((-8231/524288 : ℝ)/8) ∧ Real.exp ((-8231/524288 : ℝ)/8) ≤ (31188734405284439/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8231/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0235_exp_lower : (920114110606241761/1000000000000000000 : ℝ) ≤ Real.exp ((-21313941340899/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313941340899/32000000000000 : ℝ)/8) ≤ (460057055303120881/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313941340899/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0235_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054913375907/1000000000000 : ℝ) ≤ 4*Real.exp (16461/131072 : ℝ)*Real.exp (-mu (radius 8 (8231/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054913375907/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8231/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0235_exp_radius
  have hrNumeric : (984423206389/1000000000000 : ℝ) ≤ Real.exp (-8231/524288 : ℝ) ∧ Real.exp (-8231/524288 : ℝ) ≤ (98442320639/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984423206389/1000000000000 : ℝ) ≤ (radius 8 (8231/65536 : ℝ)) ∧ (radius 8 (8231/65536 : ℝ)) ≤ (98442320639/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8231/65536 : ℝ)) (984423206389/1000000000000 : ℝ) (98442320639/100000000000 : ℝ) (17581510379/100000000000 : ℝ) (175815103797/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8231/65536 : ℝ)) (984423206389/1000000000000 : ℝ) (98442320639/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984423206389/1000000000000 : ℝ) (98442320639/100000000000 : ℝ) (496105801597/500000000000 : ℝ) (198442320639/200000000000 : ℝ) (62011314693/62500000000 : ℝ) (992181035089/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 1 (496105801597/500000000000 : ℝ) (198442320639/200000000000 : ℝ) (62011314693/62500000000 : ℝ) (992181035089/1000000000000 : ℝ) (992196319141/1000000000000 : ℝ) (496098159571/500000000000 : ℝ) (992196319023/1000000000000 : ℝ) (39687852761/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 2 (992196319141/1000000000000 : ℝ) (496098159571/500000000000 : ℝ) (992196319023/1000000000000 : ℝ) (39687852761/40000000000 : ℝ) (496098159541/500000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 3 (496098159541/500000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 4 (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 5 (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 6 (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8231/65536 : ℝ)) 7 (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8231/65536 : ℝ))) (17581510379/100000000000 : ℝ) (175815103797/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17581510379/100000000000 : ℝ) (175815103797/1000000000000 : ℝ) (117581510379/200000000000 : ℝ) (587907551899/1000000000000 : ℝ) (419303116837/1000000000000 : ℝ) (419303116847/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 1 (117581510379/200000000000 : ℝ) (587907551899/1000000000000 : ℝ) (419303116837/1000000000000 : ℝ) (419303116847/1000000000000 : ℝ) (251802667183/500000000000 : ℝ) (503605334373/1000000000000 : ℝ) (248249606707/500000000000 : ℝ) (496499213423/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 2 (251802667183/500000000000 : ℝ) (503605334373/1000000000000 : ℝ) (248249606707/500000000000 : ℝ) (496499213423/1000000000000 : ℝ) (50005227389/100000000000 : ℝ) (250026136949/500000000000 : ℝ) (500039650811/1000000000000 : ℝ) (25001982541/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 3 (50005227389/100000000000 : ℝ) (250026136949/500000000000 : ℝ) (500039650811/1000000000000 : ℝ) (25001982541/50000000000 : ℝ) (10000919247/20000000000 : ℝ) (500045962359/1000000000000 : ℝ) (50004596231/100000000000 : ℝ) (6250574529/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 4 (10000919247/20000000000 : ℝ) (500045962359/1000000000000 : ℝ) (50004596231/100000000000 : ℝ) (6250574529/12500000000 : ℝ) (50004596233/100000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 5 (50004596233/100000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 6 (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8231/65536 : ℝ))) 7 (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8231/65536 : ℝ)) hmem 8 (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8231/65536 : ℝ))) hcmem 8 (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8231/65536 : ℝ)) (992196319081/1000000000000 : ℝ) (248049079771/250000000000 : ℝ) (500045962329/1000000000000 : ℝ) (25002298117/50000000000 : ℝ) (791648130261/1000000000000 : ℝ) (395824065141/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0235_exp_lower
  have heNumeric : (2054913375907/1000000000000 : ℝ)/4 ≤ Real.exp (-21313941340899/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054913375907/1000000000000 : ℝ)/4 ≤ Real.exp ((16461/131072 : ℝ)-(395824065141/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16461/131072 : ℝ) (8231/65536 : ℝ) (395824065141/500000000000 : ℝ) (2054913375907/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0236; no trusted numerical premise.
theorem cover8_leaf0236_exp_radius : (249509845498382321/250000000000000000 : ℝ) ≤ Real.exp ((-16463/1048576 : ℝ)/8) ∧ Real.exp ((-16463/1048576 : ℝ)/8) ≤ (199607876398705857/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16463/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0236_exp_lower : (460057050418725701/500000000000000000 : ℝ) ≤ Real.exp ((-10656972029417/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656972029417/16000000000000 : ℝ)/8) ≤ (920114100837451403/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656972029417/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0236_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728300343/250000000000 : ℝ) ≤ 4*Real.exp (8231/65536 : ℝ)*Real.exp (-mu (radius 8 (16463/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728300343/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16463/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0236_exp_radius
  have hrNumeric : (984422267571/1000000000000 : ℝ) ≤ Real.exp (-16463/1048576 : ℝ) ∧ Real.exp (-16463/1048576 : ℝ) ≤ (246105566893/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984422267571/1000000000000 : ℝ) ≤ (radius 8 (16463/131072 : ℝ)) ∧ (radius 8 (16463/131072 : ℝ)) ≤ (246105566893/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16463/131072 : ℝ)) (984422267571/1000000000000 : ℝ) (246105566893/250000000000 : ℝ) (35164072067/200000000000 : ℝ) (175820360341/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16463/131072 : ℝ)) (984422267571/1000000000000 : ℝ) (246105566893/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984422267571/1000000000000 : ℝ) (246105566893/250000000000 : ℝ) (198442226757/200000000000 : ℝ) (496105566893/500000000000 : ℝ) (49609028099/50000000000 : ℝ) (992180561981/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 1 (198442226757/200000000000 : ℝ) (496105566893/500000000000 : ℝ) (49609028099/50000000000 : ℝ) (992180561981/1000000000000 : ℝ) (496097923941/500000000000 : ℝ) (248048961971/250000000000 : ℝ) (248048961941/250000000000 : ℝ) (496097923883/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 2 (496097923941/500000000000 : ℝ) (248048961971/250000000000 : ℝ) (248048961941/250000000000 : ℝ) (496097923883/500000000000 : ℝ) (992195847823/1000000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 3 (992195847823/1000000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 4 (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 5 (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 6 (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16463/131072 : ℝ)) 7 (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16463/131072 : ℝ))) (35164072067/200000000000 : ℝ) (175820360341/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35164072067/200000000000 : ℝ) (175820360341/1000000000000 : ℝ) (587910180167/1000000000000 : ℝ) (587910180171/1000000000000 : ℝ) (419309384983/1000000000000 : ℝ) (419309384991/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 1 (587910180167/1000000000000 : ℝ) (587910180171/1000000000000 : ℝ) (419309384983/1000000000000 : ℝ) (419309384991/1000000000000 : ℝ) (20144391303/40000000000 : ℝ) (503609782581/1000000000000 : ℝ) (248252017147/500000000000 : ℝ) (248252017151/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 2 (20144391303/40000000000 : ℝ) (503609782581/1000000000000 : ℝ) (248252017147/500000000000 : ℝ) (248252017151/500000000000 : ℝ) (250028454217/500000000000 : ℝ) (250028454221/500000000000 : ℝ) (500044286797/1000000000000 : ℝ) (100008857361/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 3 (250028454217/500000000000 : ℝ) (250028454221/500000000000 : ℝ) (500044286797/1000000000000 : ℝ) (100008857361/200000000000 : ℝ) (100010119523/200000000000 : ℝ) (62506324703/125000000000 : ℝ) (20002023903/40000000000 : ℝ) (31253162349/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 4 (100010119523/200000000000 : ℝ) (62506324703/125000000000 : ℝ) (20002023903/40000000000 : ℝ) (31253162349/62500000000 : ℝ) (100010119519/200000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 5 (100010119519/200000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 6 (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16463/131072 : ℝ))) 7 (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16463/131072 : ℝ)) hmem 8 (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16463/131072 : ℝ))) hcmem 8 (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16463/131072 : ℝ)) (496097923911/500000000000 : ℝ) (39687833913/40000000000 : ℝ) (250025298797/500000000000 : ℝ) (125012649401/250000000000 : ℝ) (791655844593/1000000000000 : ℝ) (197913961153/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0236_exp_lower
  have heNumeric : (513728300343/250000000000 : ℝ)/4 ≤ Real.exp (-10656972029417/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728300343/250000000000 : ℝ)/4 ≤ Real.exp ((8231/65536 : ℝ)-(197913961153/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8231/65536 : ℝ) (16463/131072 : ℝ) (197913961153/250000000000 : ℝ) (513728300343/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0237; no trusted numerical premise.
theorem cover8_leaf0237_exp_radius : (62377453938623169/62500000000000000 : ℝ) ≤ Real.exp ((-1029/65536 : ℝ)/8) ∧ Real.exp ((-1029/65536 : ℝ)/8) ≤ (199607852603594141/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1029/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0237_exp_lower : (920114091104315567/1000000000000000000 : ℝ) ≤ Real.exp ((-21313946766849/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313946766849/32000000000000 : ℝ)/8) ≤ (57507130694019723/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313946766849/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0237_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456513737/500000000000 : ℝ) ≤ 4*Real.exp (16463/131072 : ℝ)*Real.exp (-mu (radius 8 (1029/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456513737/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1029/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0237_exp_radius
  have hrNumeric : (984421328753/1000000000000 : ℝ) ≤ Real.exp (-1029/65536 : ℝ) ∧ Real.exp (-1029/65536 : ℝ) ≤ (492210664377/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984421328753/1000000000000 : ℝ) ≤ (radius 8 (1029/8192 : ℝ)) ∧ (radius 8 (1029/8192 : ℝ)) ≤ (492210664377/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1029/8192 : ℝ)) (984421328753/1000000000000 : ℝ) (492210664377/500000000000 : ℝ) (175825616717/1000000000000 : ℝ) (43956404181/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1029/8192 : ℝ)) (984421328753/1000000000000 : ℝ) (492210664377/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984421328753/1000000000000 : ℝ) (492210664377/500000000000 : ℝ) (124026333047/125000000000 : ℝ) (992210664377/1000000000000 : ℝ) (992180088871/1000000000000 : ℝ) (124022511109/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 1 (124026333047/125000000000 : ℝ) (992210664377/1000000000000 : ℝ) (992180088871/1000000000000 : ℝ) (124022511109/125000000000 : ℝ) (992195376623/1000000000000 : ℝ) (7937563013/8000000000 : ℝ) (198439075301/200000000000 : ℝ) (992195376507/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 2 (992195376623/1000000000000 : ℝ) (7937563013/8000000000 : ℝ) (198439075301/200000000000 : ℝ) (992195376507/1000000000000 : ℝ) (248048844141/250000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 3 (248048844141/250000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 4 (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 5 (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 6 (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1029/8192 : ℝ)) 7 (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1029/8192 : ℝ))) (175825616717/1000000000000 : ℝ) (43956404181/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175825616717/1000000000000 : ℝ) (43956404181/250000000000 : ℝ) (293956404179/500000000000 : ℝ) (293956404181/500000000000 : ℝ) (10482891321/25000000000 : ℝ) (419315652849/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 1 (293956404179/500000000000 : ℝ) (293956404181/500000000000 : ℝ) (10482891321/25000000000 : ℝ) (419315652849/1000000000000 : ℝ) (503614230599/1000000000000 : ℝ) (251807115303/500000000000 : ℝ) (99301770991/200000000000 : ℝ) (496508854963/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 2 (503614230599/1000000000000 : ℝ) (251807115303/500000000000 : ℝ) (99301770991/200000000000 : ℝ) (496508854963/1000000000000 : ℝ) (500061542777/1000000000000 : ℝ) (100012308557/200000000000 : ℝ) (25002446129/50000000000 : ℝ) (125012230647/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 3 (500061542777/1000000000000 : ℝ) (100012308557/200000000000 : ℝ) (25002446129/50000000000 : ℝ) (125012230647/250000000000 : ℝ) (250027616339/500000000000 : ℝ) (500055232687/1000000000000 : ℝ) (250027616319/500000000000 : ℝ) (500055232647/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 4 (250027616339/500000000000 : ℝ) (500055232687/1000000000000 : ℝ) (250027616319/500000000000 : ℝ) (500055232647/1000000000000 : ℝ) (250027616329/500000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 5 (250027616329/500000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 6 (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1029/8192 : ℝ))) 7 (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1029/8192 : ℝ)) hmem 8 (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1029/8192 : ℝ))) hcmem 8 (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1029/8192 : ℝ)) (992195376563/1000000000000 : ℝ) (496097688283/500000000000 : ℝ) (500055232657/1000000000000 : ℝ) (500055232667/1000000000000 : ℝ) (791663558613/1000000000000 : ℝ) (98957944829/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0237_exp_lower
  have heNumeric : (1027456513737/500000000000 : ℝ)/4 ≤ Real.exp (-21313946766849/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456513737/500000000000 : ℝ)/4 ≤ Real.exp ((16463/131072 : ℝ)-(98957944829/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16463/131072 : ℝ) (1029/8192 : ℝ) (98957944829/125000000000 : ℝ) (1027456513737/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0238; no trusted numerical premise.
theorem cover8_leaf0238_exp_radius : (249509786010606577/250000000000000000 : ℝ) ≤ Real.exp ((-16465/1048576 : ℝ)/8) ∧ Real.exp ((-16465/1048576 : ℝ)/8) ≤ (998039144042426309/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16465/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0238_exp_lower : (460057040703762171/500000000000000000 : ℝ) ≤ Real.exp ((-1332121841547/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332121841547/2000000000000 : ℝ)/8) ≤ (920114081407524343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332121841547/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0238_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456427113/500000000000 : ℝ) ≤ 4*Real.exp (1029/8192 : ℝ)*Real.exp (-mu (radius 8 (16465/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456427113/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16465/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0238_exp_radius
  have hrNumeric : (61526274371/62500000000 : ℝ) ≤ Real.exp (-16465/1048576 : ℝ) ∧ Real.exp (-16465/1048576 : ℝ) ≤ (984420389937/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61526274371/62500000000 : ℝ) ≤ (radius 8 (16465/131072 : ℝ)) ∧ (radius 8 (16465/131072 : ℝ)) ≤ (984420389937/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16465/131072 : ℝ)) (61526274371/62500000000 : ℝ) (984420389937/1000000000000 : ℝ) (43957718233/250000000000 : ℝ) (175830872939/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16465/131072 : ℝ)) (61526274371/62500000000 : ℝ) (984420389937/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61526274371/62500000000 : ℝ) (984420389937/1000000000000 : ℝ) (124026274371/125000000000 : ℝ) (992210194969/1000000000000 : ℝ) (992179615763/1000000000000 : ℝ) (248044903941/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 1 (124026274371/125000000000 : ℝ) (992210194969/1000000000000 : ℝ) (992179615763/1000000000000 : ℝ) (248044903941/250000000000 : ℝ) (198438981073/200000000000 : ℝ) (992194905367/1000000000000 : ℝ) (992194905247/1000000000000 : ℝ) (992194905249/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 2 (198438981073/200000000000 : ℝ) (992194905367/1000000000000 : ℝ) (992194905247/1000000000000 : ℝ) (992194905249/1000000000000 : ℝ) (496097452653/500000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 3 (496097452653/500000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 4 (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 5 (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 6 (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16465/131072 : ℝ)) 7 (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16465/131072 : ℝ))) (43957718233/250000000000 : ℝ) (175830872939/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43957718233/250000000000 : ℝ) (175830872939/1000000000000 : ℝ) (293957718233/500000000000 : ℝ) (58791543647/100000000000 : ℝ) (104830480101/250000000000 : ℝ) (209660960207/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 1 (293957718233/500000000000 : ℝ) (58791543647/100000000000 : ℝ) (104830480101/250000000000 : ℝ) (209660960207/500000000000 : ℝ) (100723735687/200000000000 : ℝ) (251809339221/500000000000 : ℝ) (248256837697/500000000000 : ℝ) (496513675403/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 2 (100723735687/200000000000 : ℝ) (251809339221/500000000000 : ℝ) (248256837697/500000000000 : ℝ) (496513675403/1000000000000 : ℝ) (250033088457/500000000000 : ℝ) (500066176923/1000000000000 : ℝ) (250026779079/500000000000 : ℝ) (500053558167/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 3 (250033088457/500000000000 : ℝ) (500066176923/1000000000000 : ℝ) (250026779079/500000000000 : ℝ) (500053558167/1000000000000 : ℝ) (31253741721/62500000000 : ℝ) (100011973509/200000000000 : ℝ) (62507483437/125000000000 : ℝ) (250029933753/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 4 (31253741721/62500000000 : ℝ) (100011973509/200000000000 : ℝ) (62507483437/125000000000 : ℝ) (250029933753/500000000000 : ℝ) (125014966879/250000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 5 (125014966879/250000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 6 (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16465/131072 : ℝ))) 7 (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16465/131072 : ℝ)) hmem 8 (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16465/131072 : ℝ))) hcmem 8 (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16465/131072 : ℝ)) (198438981061/200000000000 : ℝ) (248048726327/250000000000 : ℝ) (100011973503/200000000000 : ℝ) (250029933763/500000000000 : ℝ) (158334254463/200000000000 : ℝ) (49479454521/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0238_exp_lower
  have heNumeric : (1027456427113/500000000000 : ℝ)/4 ≤ Real.exp (-1332121841547/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456427113/500000000000 : ℝ)/4 ≤ Real.exp ((1029/8192 : ℝ)-(49479454521/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1029/8192 : ℝ) (16465/131072 : ℝ) (49479454521/62500000000 : ℝ) (1027456427113/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0239; no trusted numerical premise.
theorem cover8_leaf0239_exp_radius : (499019512533448047/500000000000000000 : ℝ) ≤ Real.exp ((-8233/524288 : ℝ)/8) ∧ Real.exp ((-8233/524288 : ℝ)/8) ≤ (199607805013379219/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8233/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0239_exp_lower : (36804562869915313/40000000000000000 : ℝ) ≤ Real.exp ((-21313952152319/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313952152319/32000000000000 : ℝ)/8) ≤ (460057035873941413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313952152319/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0239_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912681641/1000000000000 : ℝ) ≤ 4*Real.exp (16465/131072 : ℝ)*Real.exp (-mu (radius 8 (8233/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912681641/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8233/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0239_exp_radius
  have hrNumeric : (12305243139/12500000000 : ℝ) ≤ Real.exp (-8233/524288 : ℝ) ∧ Real.exp (-8233/524288 : ℝ) ≤ (984419451121/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12305243139/12500000000 : ℝ) ≤ (radius 8 (8233/65536 : ℝ)) ∧ (radius 8 (8233/65536 : ℝ)) ≤ (984419451121/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8233/65536 : ℝ)) (12305243139/12500000000 : ℝ) (984419451121/1000000000000 : ℝ) (175836128979/1000000000000 : ℝ) (87918064493/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8233/65536 : ℝ)) (12305243139/12500000000 : ℝ) (984419451121/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12305243139/12500000000 : ℝ) (984419451121/1000000000000 : ℝ) (24805243139/25000000000 : ℝ) (992209725561/1000000000000 : ℝ) (198435828531/200000000000 : ℝ) (242231236/244140625 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 1 (24805243139/25000000000 : ℝ) (992209725561/1000000000000 : ℝ) (198435828531/200000000000 : ℝ) (242231236/244140625 : ℝ) (992194434107/1000000000000 : ℝ) (992194434109/1000000000000 : ℝ) (992194433989/1000000000000 : ℝ) (992194433991/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 2 (992194434107/1000000000000 : ℝ) (992194434109/1000000000000 : ℝ) (992194433989/1000000000000 : ℝ) (992194433991/1000000000000 : ℝ) (968939877/976562500 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 3 (968939877/976562500 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 4 (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 5 (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 6 (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8233/65536 : ℝ)) 7 (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8233/65536 : ℝ))) (175836128979/1000000000000 : ℝ) (87918064493/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175836128979/1000000000000 : ℝ) (87918064493/500000000000 : ℝ) (587918064489/1000000000000 : ℝ) (587918064493/1000000000000 : ℝ) (16773127507/40000000000 : ℝ) (104832046921/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 1 (587918064489/1000000000000 : ℝ) (587918064493/1000000000000 : ℝ) (16773127507/40000000000 : ℝ) (104832046921/250000000000 : ℝ) (251811563041/500000000000 : ℝ) (503623126089/1000000000000 : ℝ) (49651849561/100000000000 : ℝ) (248259247809/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 2 (251811563041/500000000000 : ℝ) (503623126089/1000000000000 : ℝ) (49651849561/100000000000 : ℝ) (248259247809/500000000000 : ℝ) (250035405423/500000000000 : ℝ) (250035405427/500000000000 : ℝ) (50005819353/100000000000 : ℝ) (250029096769/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 3 (250035405423/500000000000 : ℝ) (250035405427/500000000000 : ℝ) (50005819353/100000000000 : ℝ) (250029096769/500000000000 : ℝ) (125016125547/250000000000 : ℝ) (125016125549/250000000000 : ℝ) (125016125537/250000000000 : ℝ) (500064502157/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 4 (125016125547/250000000000 : ℝ) (125016125549/250000000000 : ℝ) (125016125537/250000000000 : ℝ) (500064502157/1000000000000 : ℝ) (62508062771/125000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 5 (62508062771/125000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 6 (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8233/65536 : ℝ))) 7 (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8233/65536 : ℝ)) hmem 8 (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8233/65536 : ℝ))) hcmem 8 (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8233/65536 : ℝ)) (992194434047/1000000000000 : ℝ) (19843888681/20000000000 : ℝ) (500064502167/1000000000000 : ℝ) (500064502177/1000000000000 : ℝ) (395839492849/500000000000 : ℝ) (791678985717/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0239_exp_lower
  have heNumeric : (2054912681641/1000000000000 : ℝ)/4 ≤ Real.exp (-21313952152319/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912681641/1000000000000 : ℝ)/4 ≤ Real.exp ((16465/131072 : ℝ)-(791678985717/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16465/131072 : ℝ) (8233/65536 : ℝ) (791678985717/1000000000000 : ℝ) (2054912681641/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0240; no trusted numerical premise.
theorem cover8_leaf0240_exp_radius : (998038906091380063/1000000000000000000 : ℝ) ≤ Real.exp ((-16467/1048576 : ℝ)/8) ∧ Real.exp ((-16467/1048576 : ℝ)/8) ≤ (31188715815355627/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16467/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0240_exp_lower : (920114062124815943/1000000000000000000 : ℝ) ≤ Real.exp ((-2131395482971/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131395482971/3200000000000 : ℝ)/8) ≤ (115014257765601993/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131395482971/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0240_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912509709/1000000000000 : ℝ) ≤ 4*Real.exp (8233/65536 : ℝ)*Real.exp (-mu (radius 8 (16467/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912509709/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16467/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0240_exp_radius
  have hrNumeric : (196883702461/200000000000 : ℝ) ≤ Real.exp (-16467/1048576 : ℝ) ∧ Real.exp (-16467/1048576 : ℝ) ≤ (492209256153/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196883702461/200000000000 : ℝ) ≤ (radius 8 (16467/131072 : ℝ)) ∧ (radius 8 (16467/131072 : ℝ)) ≤ (492209256153/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16467/131072 : ℝ)) (196883702461/200000000000 : ℝ) (492209256153/500000000000 : ℝ) (175841384859/1000000000000 : ℝ) (35168276973/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16467/131072 : ℝ)) (196883702461/200000000000 : ℝ) (492209256153/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196883702461/200000000000 : ℝ) (492209256153/500000000000 : ℝ) (124026157019/125000000000 : ℝ) (992209256153/1000000000000 : ℝ) (992178669547/1000000000000 : ℝ) (248044667387/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 1 (124026157019/125000000000 : ℝ) (992209256153/1000000000000 : ℝ) (992178669547/1000000000000 : ℝ) (248044667387/250000000000 : ℝ) (992193962849/1000000000000 : ℝ) (992193962851/1000000000000 : ℝ) (992193962731/1000000000000 : ℝ) (992193962733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 2 (992193962849/1000000000000 : ℝ) (992193962851/1000000000000 : ℝ) (992193962731/1000000000000 : ℝ) (992193962733/1000000000000 : ℝ) (99219396279/100000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 3 (99219396279/100000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 4 (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 5 (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 6 (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16467/131072 : ℝ)) 7 (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16467/131072 : ℝ))) (175841384859/1000000000000 : ℝ) (35168276973/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175841384859/1000000000000 : ℝ) (35168276973/200000000000 : ℝ) (587920692429/1000000000000 : ℝ) (587920692433/1000000000000 : ℝ) (104833613663/250000000000 : ℝ) (419334454661/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 1 (587920692429/1000000000000 : ℝ) (587920692433/1000000000000 : ℝ) (104833613663/250000000000 : ℝ) (419334454661/1000000000000 : ℝ) (25181378677/50000000000 : ℝ) (503627573547/1000000000000 : ℝ) (496523315603/1000000000000 : ℝ) (496523315611/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 2 (25181378677/50000000000 : ℝ) (503627573547/1000000000000 : ℝ) (496523315603/1000000000000 : ℝ) (496523315611/1000000000000 : ℝ) (500075444571/1000000000000 : ℝ) (500075444579/1000000000000 : ℝ) (100012565739/200000000000 : ℝ) (15626963397/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 3 (500075444571/1000000000000 : ℝ) (500075444579/1000000000000 : ℝ) (100012565739/200000000000 : ℝ) (15626963397/31250000000 : ℝ) (500069136633/1000000000000 : ℝ) (250034568321/500000000000 : ℝ) (500069136593/1000000000000 : ℝ) (250034568301/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 4 (500069136633/1000000000000 : ℝ) (250034568321/500000000000 : ℝ) (500069136593/1000000000000 : ℝ) (250034568301/500000000000 : ℝ) (500069136613/1000000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 5 (500069136613/1000000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 6 (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16467/131072 : ℝ))) 7 (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16467/131072 : ℝ)) hmem 8 (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16467/131072 : ℝ))) hcmem 8 (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16467/131072 : ℝ)) (992193962789/1000000000000 : ℝ) (124024245349/125000000000 : ℝ) (125017284153/250000000000 : ℝ) (250034568311/500000000000 : ℝ) (791686698761/1000000000000 : ℝ) (39584334939/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0240_exp_lower
  have heNumeric : (2054912509709/1000000000000 : ℝ)/4 ≤ Real.exp (-2131395482971/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912509709/1000000000000 : ℝ)/4 ≤ Real.exp ((8233/65536 : ℝ)-(39584334939/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8233/65536 : ℝ) (16467/131072 : ℝ) (39584334939/50000000000 : ℝ) (2054912509709/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0241; no trusted numerical premise.
theorem cover8_leaf0241_exp_radius : (124754848389484777/125000000000000000 : ℝ) ≤ Real.exp ((-4117/262144 : ℝ)/8) ∧ Real.exp ((-4117/262144 : ℝ)/8) ≤ (998038787115878217/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4117/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0241_exp_lower : (920114052538208681/1000000000000000000 : ℝ) ≤ Real.exp ((-21313957496957/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313957496957/32000000000000 : ℝ)/8) ≤ (460057026269104341/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313957496957/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0241_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912338429/1000000000000 : ℝ) ≤ 4*Real.exp (16467/131072 : ℝ)*Real.exp (-mu (radius 8 (4117/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912338429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4117/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0241_exp_radius
  have hrNumeric : (984417573491/1000000000000 : ℝ) ≤ Real.exp (-4117/262144 : ℝ) ∧ Real.exp (-4117/262144 : ℝ) ≤ (246104393373/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984417573491/1000000000000 : ℝ) ≤ (radius 8 (4117/32768 : ℝ)) ∧ (radius 8 (4117/32768 : ℝ)) ≤ (246104393373/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4117/32768 : ℝ)) (984417573491/1000000000000 : ℝ) (246104393373/250000000000 : ℝ) (175846640571/1000000000000 : ℝ) (175846640577/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4117/32768 : ℝ)) (984417573491/1000000000000 : ℝ) (246104393373/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984417573491/1000000000000 : ℝ) (246104393373/250000000000 : ℝ) (198441757349/200000000000 : ℝ) (496104393373/500000000000 : ℝ) (24804454911/25000000000 : ℝ) (992178196441/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 1 (198441757349/200000000000 : ℝ) (496104393373/500000000000 : ℝ) (24804454911/25000000000 : ℝ) (992178196441/1000000000000 : ℝ) (124024186449/125000000000 : ℝ) (496096745797/500000000000 : ℝ) (496096745737/500000000000 : ℝ) (248048372869/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 2 (124024186449/125000000000 : ℝ) (496096745797/500000000000 : ℝ) (496096745737/500000000000 : ℝ) (248048372869/250000000000 : ℝ) (992193491533/1000000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 3 (992193491533/1000000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 4 (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 5 (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 6 (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4117/32768 : ℝ)) 7 (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4117/32768 : ℝ))) (175846640571/1000000000000 : ℝ) (175846640577/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175846640571/1000000000000 : ℝ) (175846640577/1000000000000 : ℝ) (117584664057/200000000000 : ℝ) (587923320289/1000000000000 : ℝ) (52417590167/125000000000 : ℝ) (6552198771/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 1 (117584664057/200000000000 : ℝ) (587923320289/1000000000000 : ℝ) (52417590167/125000000000 : ℝ) (6552198771/15625000000 : ℝ) (50363202081/100000000000 : ℝ) (503632020817/1000000000000 : ℝ) (248264067687/500000000000 : ℝ) (248264067691/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 2 (50363202081/100000000000 : ℝ) (503632020817/1000000000000 : ℝ) (248264067687/500000000000 : ℝ) (248264067691/500000000000 : ℝ) (125020019523/250000000000 : ℝ) (5000800781/10000000000 : ℝ) (62508432957/125000000000 : ℝ) (31254216479/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 3 (125020019523/250000000000 : ℝ) (5000800781/10000000000 : ℝ) (62508432957/125000000000 : ℝ) (31254216479/62500000000 : ℝ) (250036885437/500000000000 : ℝ) (250036885441/500000000000 : ℝ) (250036885417/500000000000 : ℝ) (500073770843/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 4 (250036885437/500000000000 : ℝ) (250036885441/500000000000 : ℝ) (250036885417/500000000000 : ℝ) (500073770843/1000000000000 : ℝ) (250036885427/500000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 5 (250036885427/500000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 6 (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4117/32768 : ℝ))) 7 (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4117/32768 : ℝ)) hmem 8 (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4117/32768 : ℝ))) hcmem 8 (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4117/32768 : ℝ)) (248048372883/250000000000 : ℝ) (198438698307/200000000000 : ℝ) (500073770853/1000000000000 : ℝ) (500073770863/1000000000000 : ℝ) (791694411507/1000000000000 : ℝ) (395847205763/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0241_exp_lower
  have heNumeric : (2054912338429/1000000000000 : ℝ)/4 ≤ Real.exp (-21313957496957/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912338429/1000000000000 : ℝ)/4 ≤ Real.exp ((16467/131072 : ℝ)-(395847205763/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16467/131072 : ℝ) (4117/32768 : ℝ) (395847205763/500000000000 : ℝ) (2054912338429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0242; no trusted numerical premise.
theorem cover8_leaf0242_exp_radius : (998038668140390551/1000000000000000000 : ℝ) ≤ Real.exp ((-16469/1048576 : ℝ)/8) ∧ Real.exp ((-16469/1048576 : ℝ)/8) ≤ (124754833517548819/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16469/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0242_exp_lower : (460057021493742983/500000000000000000 : ℝ) ≤ Real.exp ((-1065698007711/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065698007711/1600000000000 : ℝ)/8) ≤ (920114042987485967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065698007711/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0242_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912167791/1000000000000 : ℝ) ≤ 4*Real.exp (4117/32768 : ℝ)*Real.exp (-mu (radius 8 (16469/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912167791/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16469/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0242_exp_radius
  have hrNumeric : (984416634677/1000000000000 : ℝ) ≤ Real.exp (-16469/1048576 : ℝ) ∧ Real.exp (-16469/1048576 : ℝ) ≤ (492208317339/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984416634677/1000000000000 : ℝ) ≤ (radius 8 (16469/131072 : ℝ)) ∧ (radius 8 (16469/131072 : ℝ)) ≤ (492208317339/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16469/131072 : ℝ)) (984416634677/1000000000000 : ℝ) (492208317339/500000000000 : ℝ) (4396297403/25000000000 : ℝ) (175851896127/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16469/131072 : ℝ)) (984416634677/1000000000000 : ℝ) (492208317339/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984416634677/1000000000000 : ℝ) (492208317339/500000000000 : ℝ) (496104158669/500000000000 : ℝ) (992208317339/1000000000000 : ℝ) (248044430833/250000000000 : ℝ) (992177723333/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 1 (496104158669/500000000000 : ℝ) (992208317339/1000000000000 : ℝ) (248044430833/250000000000 : ℝ) (992177723333/1000000000000 : ℝ) (198438604067/200000000000 : ℝ) (62012063771/62500000000 : ℝ) (992193020217/1000000000000 : ℝ) (992193020219/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 2 (198438604067/200000000000 : ℝ) (62012063771/62500000000 : ℝ) (992193020217/1000000000000 : ℝ) (992193020219/1000000000000 : ℝ) (248048255069/250000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 3 (248048255069/250000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 4 (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 5 (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 6 (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16469/131072 : ℝ)) 7 (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16469/131072 : ℝ))) (4396297403/25000000000 : ℝ) (175851896127/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4396297403/25000000000 : ℝ) (175851896127/1000000000000 : ℝ) (29396297403/50000000000 : ℝ) (18372685877/31250000000 : ℝ) (104836746933/250000000000 : ℝ) (419346987741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 1 (29396297403/50000000000 : ℝ) (18372685877/31250000000 : ℝ) (104836746933/250000000000 : ℝ) (419346987741/1000000000000 : ℝ) (62954558487/125000000000 : ℝ) (503636467903/1000000000000 : ℝ) (248266477463/500000000000 : ℝ) (248266477467/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 2 (62954558487/125000000000 : ℝ) (503636467903/1000000000000 : ℝ) (248266477463/500000000000 : ℝ) (248266477467/500000000000 : ℝ) (500084711411/1000000000000 : ℝ) (500084711419/1000000000000 : ℝ) (250036049207/500000000000 : ℝ) (500072098423/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 3 (500084711411/1000000000000 : ℝ) (500084711419/1000000000000 : ℝ) (250036049207/500000000000 : ℝ) (500072098423/1000000000000 : ℝ) (31254900307/62500000000 : ℝ) (500078404921/1000000000000 : ℝ) (62509800609/125000000000 : ℝ) (250039202441/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 4 (31254900307/62500000000 : ℝ) (500078404921/1000000000000 : ℝ) (62509800609/125000000000 : ℝ) (250039202441/500000000000 : ℝ) (125019601223/250000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 5 (125019601223/250000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 6 (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16469/131072 : ℝ))) 7 (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16469/131072 : ℝ)) hmem 8 (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16469/131072 : ℝ))) hcmem 8 (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16469/131072 : ℝ)) (39687720811/40000000000 : ℝ) (496096510139/500000000000 : ℝ) (500078404891/1000000000000 : ℝ) (250039202451/500000000000 : ℝ) (791702123939/1000000000000 : ℝ) (19792553099/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0242_exp_lower
  have heNumeric : (2054912167791/1000000000000 : ℝ)/4 ≤ Real.exp (-1065698007711/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912167791/1000000000000 : ℝ)/4 ≤ Real.exp ((4117/32768 : ℝ)-(19792553099/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4117/32768 : ℝ) (16469/131072 : ℝ) (19792553099/25000000000 : ℝ) (2054912167791/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0243; no trusted numerical premise.
theorem cover8_leaf0243_exp_radius : (998038549164917069/1000000000000000000 : ℝ) ≤ Real.exp ((-8235/524288 : ℝ)/8) ∧ Real.exp ((-8235/524288 : ℝ)/8) ≤ (99803854916491707/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8235/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0243_exp_lower : (230028508368593253/250000000000000000 : ℝ) ≤ Real.exp ((-21313962801019/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313962801019/32000000000000 : ℝ)/8) ≤ (920114033474373013/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313962801019/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0243_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16053999983/7812500000 : ℝ) ≤ 4*Real.exp (16469/131072 : ℝ)*Real.exp (-mu (radius 8 (8235/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (16053999983/7812500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8235/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0243_exp_radius
  have hrNumeric : (196883139173/200000000000 : ℝ) ≤ Real.exp (-8235/524288 : ℝ) ∧ Real.exp (-8235/524288 : ℝ) ≤ (492207847933/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196883139173/200000000000 : ℝ) ≤ (radius 8 (8235/65536 : ℝ)) ∧ (radius 8 (8235/65536 : ℝ)) ≤ (492207847933/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8235/65536 : ℝ)) (196883139173/200000000000 : ℝ) (492207847933/500000000000 : ℝ) (175857151497/1000000000000 : ℝ) (175857151503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8235/65536 : ℝ)) (196883139173/200000000000 : ℝ) (492207847933/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196883139173/200000000000 : ℝ) (492207847933/500000000000 : ℝ) (248051961983/250000000000 : ℝ) (992207847933/1000000000000 : ℝ) (39687090009/40000000000 : ℝ) (496088625113/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 1 (248051961983/250000000000 : ℝ) (992207847933/1000000000000 : ℝ) (39687090009/40000000000 : ℝ) (496088625113/500000000000 : ℝ) (496096274539/500000000000 : ℝ) (24804813727/25000000000 : ℝ) (6201203431/6250000000 : ℝ) (496096274481/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 2 (496096274539/500000000000 : ℝ) (24804813727/25000000000 : ℝ) (6201203431/6250000000 : ℝ) (496096274481/500000000000 : ℝ) (992192549019/1000000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 3 (992192549019/1000000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 4 (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 5 (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 6 (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8235/65536 : ℝ)) 7 (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8235/65536 : ℝ))) (175857151497/1000000000000 : ℝ) (175857151503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175857151497/1000000000000 : ℝ) (175857151503/1000000000000 : ℝ) (146982143937/250000000000 : ℝ) (73491071969/125000000000 : ℝ) (419353253829/1000000000000 : ℝ) (419353253837/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 1 (146982143937/250000000000 : ℝ) (73491071969/125000000000 : ℝ) (419353253829/1000000000000 : ℝ) (419353253837/1000000000000 : ℝ) (125910228697/250000000000 : ℝ) (100728182959/200000000000 : ℝ) (496537774251/1000000000000 : ℝ) (496537774259/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 2 (125910228697/250000000000 : ℝ) (100728182959/200000000000 : ℝ) (496537774251/1000000000000 : ℝ) (496537774259/1000000000000 : ℝ) (500089344519/1000000000000 : ℝ) (500089344527/1000000000000 : ℝ) (250038366481/500000000000 : ℝ) (500076732971/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 3 (500089344519/1000000000000 : ℝ) (500089344527/1000000000000 : ℝ) (250038366481/500000000000 : ℝ) (500076732971/1000000000000 : ℝ) (25004151937/50000000000 : ℝ) (500083038749/1000000000000 : ℝ) (5000830387/10000000000 : ℝ) (50008303871/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 4 (25004151937/50000000000 : ℝ) (500083038749/1000000000000 : ℝ) (5000830387/10000000000 : ℝ) (50008303871/100000000000 : ℝ) (195344937/390625000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 5 (195344937/390625000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 6 (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8235/65536 : ℝ))) 7 (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8235/65536 : ℝ)) hmem 8 (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8235/65536 : ℝ))) hcmem 8 (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8235/65536 : ℝ)) (496096274509/500000000000 : ℝ) (992192549021/1000000000000 : ℝ) (500083038719/1000000000000 : ℝ) (50008303873/100000000000 : ℝ) (395854918023/500000000000 : ℝ) (791709836067/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0243_exp_lower
  have heNumeric : (16053999983/7812500000 : ℝ)/4 ≤ Real.exp (-21313962801019/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16053999983/7812500000 : ℝ)/4 ≤ Real.exp ((16469/131072 : ℝ)-(791709836067/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16469/131072 : ℝ) (8235/65536 : ℝ) (791709836067/1000000000000 : ℝ) (16053999983/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0244; no trusted numerical premise.
theorem cover8_leaf0244_exp_radius : (99803843018945777/100000000000000000 : ℝ) ≤ Real.exp ((-16471/1048576 : ℝ)/8) ∧ Real.exp ((-16471/1048576 : ℝ)/8) ≤ (998038430189457771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16471/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0244_exp_lower : (920114023997259617/1000000000000000000 : ℝ) ≤ Real.exp ((-10656982718901/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656982718901/16000000000000 : ℝ)/8) ≤ (460057011998629809/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656982718901/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0244_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (4109823657/2000000000 : ℝ) ≤ 4*Real.exp (8235/65536 : ℝ)*Real.exp (-mu (radius 8 (16471/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (4109823657/2000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16471/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0244_exp_radius
  have hrNumeric : (984414757053/1000000000000 : ℝ) ≤ Real.exp (-16471/1048576 : ℝ) ∧ Real.exp (-16471/1048576 : ℝ) ≤ (492207378527/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984414757053/1000000000000 : ℝ) ≤ (radius 8 (16471/131072 : ℝ)) ∧ (radius 8 (16471/131072 : ℝ)) ≤ (492207378527/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16471/131072 : ℝ)) (984414757053/1000000000000 : ℝ) (492207378527/500000000000 : ℝ) (175862406711/1000000000000 : ℝ) (175862406717/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16471/131072 : ℝ)) (984414757053/1000000000000 : ℝ) (492207378527/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984414757053/1000000000000 : ℝ) (492207378527/500000000000 : ℝ) (496103689263/500000000000 : ℝ) (992207378527/1000000000000 : ℝ) (496088388559/500000000000 : ℝ) (992176777119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 1 (496103689263/500000000000 : ℝ) (992207378527/1000000000000 : ℝ) (496088388559/500000000000 : ℝ) (992176777119/1000000000000 : ℝ) (496096038911/500000000000 : ℝ) (992192077823/1000000000000 : ℝ) (124024009713/125000000000 : ℝ) (496096038853/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 2 (496096038911/500000000000 : ℝ) (992192077823/1000000000000 : ℝ) (124024009713/125000000000 : ℝ) (496096038853/500000000000 : ℝ) (992192077763/1000000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 3 (992192077763/1000000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 4 (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 5 (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 6 (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16471/131072 : ℝ)) 7 (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16471/131072 : ℝ))) (175862406711/1000000000000 : ℝ) (175862406717/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175862406711/1000000000000 : ℝ) (175862406717/1000000000000 : ℝ) (117586240671/200000000000 : ℝ) (587931203359/1000000000000 : ℝ) (419359519637/1000000000000 : ℝ) (209679759823/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 1 (117586240671/200000000000 : ℝ) (587931203359/1000000000000 : ℝ) (419359519637/1000000000000 : ℝ) (209679759823/500000000000 : ℝ) (62955670187/125000000000 : ℝ) (503645361503/1000000000000 : ℝ) (496542593357/1000000000000 : ℝ) (99308518673/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 2 (62955670187/125000000000 : ℝ) (503645361503/1000000000000 : ℝ) (496542593357/1000000000000 : ℝ) (99308518673/200000000000 : ℝ) (250046988713/500000000000 : ℝ) (250046988717/500000000000 : ℝ) (125020341827/250000000000 : ℝ) (500081367317/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 3 (250046988713/500000000000 : ℝ) (250046988717/500000000000 : ℝ) (125020341827/250000000000 : ℝ) (500081367317/1000000000000 : ℝ) (500087672367/1000000000000 : ℝ) (62510959047/125000000000 : ℝ) (500087672327/1000000000000 : ℝ) (31255479521/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 4 (500087672367/1000000000000 : ℝ) (62510959047/125000000000 : ℝ) (500087672327/1000000000000 : ℝ) (31255479521/62500000000 : ℝ) (500087672347/1000000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 5 (500087672347/1000000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 6 (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16471/131072 : ℝ))) 7 (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16471/131072 : ℝ)) hmem 8 (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16471/131072 : ℝ))) hcmem 8 (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16471/131072 : ℝ)) (496096038881/500000000000 : ℝ) (198438415553/200000000000 : ℝ) (250043836173/500000000000 : ℝ) (125021918089/250000000000 : ℝ) (395858773921/500000000000 : ℝ) (791717547861/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0244_exp_lower
  have heNumeric : (4109823657/2000000000 : ℝ)/4 ≤ Real.exp (-10656982718901/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (4109823657/2000000000 : ℝ)/4 ≤ Real.exp ((8235/65536 : ℝ)-(791717547861/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8235/65536 : ℝ) (16471/131072 : ℝ) (791717547861/1000000000000 : ℝ) (4109823657/2000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0245; no trusted numerical premise.
theorem cover8_leaf0245_exp_radius : (199607662242802531/200000000000000000 : ℝ) ≤ Real.exp ((-2059/131072 : ℝ)/8) ∧ Real.exp ((-2059/131072 : ℝ)/8) ≤ (62377394450875791/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2059/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0245_exp_lower : (460057007278705469/500000000000000000 : ℝ) ≤ Real.exp ((-21313968064217/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313968064217/32000000000000 : ℝ)/8) ≤ (920114014557410939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313968064217/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0245_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455829921/500000000000 : ℝ) ≤ 4*Real.exp (16471/131072 : ℝ)*Real.exp (-mu (radius 8 (2059/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455829921/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2059/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0245_exp_radius
  have hrNumeric : (984413818243/1000000000000 : ℝ) ≤ Real.exp (-2059/131072 : ℝ) ∧ Real.exp (-2059/131072 : ℝ) ≤ (246103454561/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984413818243/1000000000000 : ℝ) ≤ (radius 8 (2059/16384 : ℝ)) ∧ (radius 8 (2059/16384 : ℝ)) ≤ (246103454561/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2059/16384 : ℝ)) (984413818243/1000000000000 : ℝ) (246103454561/250000000000 : ℝ) (21983457719/125000000000 : ℝ) (175867661759/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2059/16384 : ℝ)) (984413818243/1000000000000 : ℝ) (246103454561/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984413818243/1000000000000 : ℝ) (246103454561/250000000000 : ℝ) (992206909121/1000000000000 : ℝ) (496103454561/500000000000 : ℝ) (248044076003/250000000000 : ℝ) (992176304013/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 1 (992206909121/1000000000000 : ℝ) (496103454561/500000000000 : ℝ) (248044076003/250000000000 : ℝ) (992176304013/1000000000000 : ℝ) (496095803283/500000000000 : ℝ) (124023950821/125000000000 : ℝ) (62011975403/62500000000 : ℝ) (19843832129/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 2 (496095803283/500000000000 : ℝ) (124023950821/125000000000 : ℝ) (62011975403/62500000000 : ℝ) (19843832129/20000000000 : ℝ) (992191606507/1000000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 3 (992191606507/1000000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 4 (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 5 (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 6 (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2059/16384 : ℝ)) 7 (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2059/16384 : ℝ))) (21983457719/125000000000 : ℝ) (175867661759/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21983457719/125000000000 : ℝ) (175867661759/1000000000000 : ℝ) (146983457719/250000000000 : ℝ) (3674586443/6250000000 : ℝ) (419365785147/1000000000000 : ℝ) (104841446289/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 1 (146983457719/250000000000 : ℝ) (3674586443/6250000000 : ℝ) (419365785147/1000000000000 : ℝ) (104841446289/250000000000 : ℝ) (503649808011/1000000000000 : ℝ) (251824904009/500000000000 : ℝ) (496547412237/1000000000000 : ℝ) (99309482449/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 2 (503649808011/1000000000000 : ℝ) (251824904009/500000000000 : ℝ) (496547412237/1000000000000 : ℝ) (99309482449/200000000000 : ℝ) (125024652531/250000000000 : ℝ) (125024652533/250000000000 : ℝ) (100017200289/200000000000 : ℝ) (500086001453/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 3 (125024652531/250000000000 : ℝ) (125024652533/250000000000 : ℝ) (100017200289/200000000000 : ℝ) (500086001453/1000000000000 : ℝ) (62511538223/125000000000 : ℝ) (500092305793/1000000000000 : ℝ) (31255769109/62500000000 : ℝ) (500092305753/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 4 (62511538223/125000000000 : ℝ) (500092305793/1000000000000 : ℝ) (31255769109/62500000000 : ℝ) (500092305753/1000000000000 : ℝ) (125023076441/250000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 5 (125023076441/250000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 6 (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2059/16384 : ℝ))) 7 (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2059/16384 : ℝ)) hmem 8 (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2059/16384 : ℝ))) hcmem 8 (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2059/16384 : ℝ)) (496095803253/500000000000 : ℝ) (992191606509/1000000000000 : ℝ) (500092305763/1000000000000 : ℝ) (500092305773/1000000000000 : ℝ) (49482828707/62500000000 : ℝ) (791725259331/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0245_exp_lower
  have heNumeric : (1027455829921/500000000000 : ℝ)/4 ≤ Real.exp (-21313968064217/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455829921/500000000000 : ℝ)/4 ≤ Real.exp ((16471/131072 : ℝ)-(791725259331/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16471/131072 : ℝ) (2059/16384 : ℝ) (791725259331/1000000000000 : ℝ) (1027455829921/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0246; no trusted numerical premise.
theorem cover8_leaf0246_exp_radius : (499019096119290861/500000000000000000 : ℝ) ≤ Real.exp ((-16473/1048576 : ℝ)/8) ∧ Real.exp ((-16473/1048576 : ℝ)/8) ≤ (998038192238581723/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16473/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0246_exp_lower : (920114005153331787/1000000000000000000 : ℝ) ≤ Real.exp ((-532849267017/800000000000 : ℝ)/8) ∧ Real.exp ((-532849267017/800000000000 : ℝ)/8) ≤ (230028501288332947/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532849267017/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0246_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054911491823/1000000000000 : ℝ) ≤ 4*Real.exp (2059/16384 : ℝ)*Real.exp (-mu (radius 8 (16473/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054911491823/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16473/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0246_exp_radius
  have hrNumeric : (984412879433/1000000000000 : ℝ) ≤ Real.exp (-16473/1048576 : ℝ) ∧ Real.exp (-16473/1048576 : ℝ) ≤ (492206439717/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984412879433/1000000000000 : ℝ) ≤ (radius 8 (16473/131072 : ℝ)) ∧ (radius 8 (16473/131072 : ℝ)) ≤ (492206439717/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16473/131072 : ℝ)) (984412879433/1000000000000 : ℝ) (492206439717/500000000000 : ℝ) (175872916631/1000000000000 : ℝ) (87936458319/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16473/131072 : ℝ)) (984412879433/1000000000000 : ℝ) (492206439717/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984412879433/1000000000000 : ℝ) (492206439717/500000000000 : ℝ) (248051609929/250000000000 : ℝ) (992206439717/1000000000000 : ℝ) (198435166181/200000000000 : ℝ) (496087915453/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 1 (248051609929/250000000000 : ℝ) (992206439717/1000000000000 : ℝ) (198435166181/200000000000 : ℝ) (496087915453/500000000000 : ℝ) (99219113531/100000000000 : ℝ) (62011945957/62500000000 : ℝ) (124023891899/125000000000 : ℝ) (496095567597/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 2 (99219113531/100000000000 : ℝ) (62011945957/62500000000 : ℝ) (124023891899/125000000000 : ℝ) (496095567597/500000000000 : ℝ) (992191135251/1000000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 3 (992191135251/1000000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 4 (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 5 (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 6 (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16473/131072 : ℝ)) 7 (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16473/131072 : ℝ))) (175872916631/1000000000000 : ℝ) (87936458319/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175872916631/1000000000000 : ℝ) (87936458319/500000000000 : ℝ) (117587291663/200000000000 : ℝ) (587936458319/1000000000000 : ℝ) (419372050369/1000000000000 : ℝ) (209686025189/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 1 (117587291663/200000000000 : ℝ) (587936458319/1000000000000 : ℝ) (419372050369/1000000000000 : ℝ) (209686025189/500000000000 : ℝ) (251827127171/500000000000 : ℝ) (503654254349/1000000000000 : ℝ) (248276115449/500000000000 : ℝ) (248276115453/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 2 (251827127171/500000000000 : ℝ) (503654254349/1000000000000 : ℝ) (248276115449/500000000000 : ℝ) (248276115453/500000000000 : ℝ) (25005162131/50000000000 : ℝ) (125025810657/250000000000 : ℝ) (25004531769/50000000000 : ℝ) (125022658847/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 3 (25005162131/50000000000 : ℝ) (125025810657/250000000000 : ℝ) (25004531769/50000000000 : ℝ) (125022658847/250000000000 : ℝ) (500096939/1000000000 : ℝ) (488375917/976562500 : ℝ) (6251211737/12500000000 : ℝ) (500096938969/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 4 (500096939/1000000000 : ℝ) (488375917/976562500 : ℝ) (6251211737/12500000000 : ℝ) (500096938969/1000000000000 : ℝ) (25004846949/50000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 5 (25004846949/50000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 6 (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16473/131072 : ℝ))) 7 (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16473/131072 : ℝ)) hmem 8 (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16473/131072 : ℝ))) hcmem 8 (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16473/131072 : ℝ)) (3968764541/4000000000 : ℝ) (992191135253/1000000000000 : ℝ) (500096938979/1000000000000 : ℝ) (500096938989/1000000000000 : ℝ) (791732970471/1000000000000 : ℝ) (79173297049/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0246_exp_lower
  have heNumeric : (2054911491823/1000000000000 : ℝ)/4 ≤ Real.exp (-532849267017/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054911491823/1000000000000 : ℝ)/4 ≤ Real.exp ((2059/16384 : ℝ)-(79173297049/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2059/16384 : ℝ) (16473/131072 : ℝ) (79173297049/100000000000 : ℝ) (2054911491823/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0247; no trusted numerical premise.
theorem cover8_leaf0247_exp_radius : (249509518315791243/250000000000000000 : ℝ) ≤ Real.exp ((-8237/524288 : ℝ)/8) ∧ Real.exp ((-8237/524288 : ℝ)/8) ≤ (998038073263164973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8237/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0247_exp_lower : (920113995786057293/1000000000000000000 : ℝ) ≤ Real.exp ((-21313973286903/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313973286903/32000000000000 : ℝ)/8) ≤ (460056997893028647/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313973286903/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0247_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455662231/500000000000 : ℝ) ≤ 4*Real.exp (16473/131072 : ℝ)*Real.exp (-mu (radius 8 (8237/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455662231/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8237/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0247_exp_radius
  have hrNumeric : (61525746289/62500000000 : ℝ) ≤ Real.exp (-8237/524288 : ℝ) ∧ Real.exp (-8237/524288 : ℝ) ≤ (315011821/320000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61525746289/62500000000 : ℝ) ≤ (radius 8 (8237/65536 : ℝ)) ∧ (radius 8 (8237/65536 : ℝ)) ≤ (315011821/320000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8237/65536 : ℝ)) (61525746289/62500000000 : ℝ) (315011821/320000000 : ℝ) (87939085671/500000000000 : ℝ) (175878171349/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8237/65536 : ℝ)) (61525746289/62500000000 : ℝ) (315011821/320000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61525746289/62500000000 : ℝ) (315011821/320000000 : ℝ) (124025746289/125000000000 : ℝ) (992205970313/1000000000000 : ℝ) (992175357799/1000000000000 : ℝ) (4960876789/5000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 1 (124025746289/125000000000 : ℝ) (992205970313/1000000000000 : ℝ) (992175357799/1000000000000 : ℝ) (4960876789/5000000000 : ℝ) (198438132811/200000000000 : ℝ) (992190664057/1000000000000 : ℝ) (992190663937/1000000000000 : ℝ) (992190663939/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 2 (198438132811/200000000000 : ℝ) (992190664057/1000000000000 : ℝ) (992190663937/1000000000000 : ℝ) (992190663939/1000000000000 : ℝ) (248047665999/250000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 3 (248047665999/250000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 4 (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 5 (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 6 (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8237/65536 : ℝ)) 7 (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8237/65536 : ℝ))) (87939085671/500000000000 : ℝ) (175878171349/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87939085671/500000000000 : ℝ) (175878171349/1000000000000 : ℝ) (587939085671/1000000000000 : ℝ) (23517563427/40000000000 : ℝ) (419378315297/1000000000000 : ℝ) (419378315307/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 1 (587939085671/1000000000000 : ℝ) (23517563427/40000000000 : ℝ) (419378315297/1000000000000 : ℝ) (419378315307/1000000000000 : ℝ) (125914675121/250000000000 : ℝ) (503658700491/1000000000000 : ℝ) (62069631167/125000000000 : ℝ) (99311409869/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 2 (125914675121/250000000000 : ℝ) (503658700491/1000000000000 : ℝ) (62069631167/125000000000 : ℝ) (99311409869/200000000000 : ℝ) (50010787491/100000000000 : ℝ) (250053937459/500000000000 : ℝ) (125023817277/250000000000 : ℝ) (500095269117/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 3 (50010787491/100000000000 : ℝ) (250053937459/500000000000 : ℝ) (125023817277/250000000000 : ℝ) (500095269117/1000000000000 : ℝ) (500101572009/1000000000000 : ℝ) (250050786009/500000000000 : ℝ) (500101571969/1000000000000 : ℝ) (250050785989/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 4 (500101572009/1000000000000 : ℝ) (250050786009/500000000000 : ℝ) (500101571969/1000000000000 : ℝ) (250050785989/500000000000 : ℝ) (500101571989/1000000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 5 (500101571989/1000000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 6 (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8237/65536 : ℝ))) 7 (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8237/65536 : ℝ)) hmem 8 (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8237/65536 : ℝ))) hcmem 8 (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8237/65536 : ℝ)) (198438132799/200000000000 : ℝ) (496095331999/500000000000 : ℝ) (125025392997/250000000000 : ℝ) (250050785999/500000000000 : ℝ) (791740681309/1000000000000 : ℝ) (791740681329/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0247_exp_lower
  have heNumeric : (1027455662231/500000000000 : ℝ)/4 ≤ Real.exp (-21313973286903/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455662231/500000000000 : ℝ)/4 ≤ Real.exp ((16473/131072 : ℝ)-(791740681329/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16473/131072 : ℝ) (8237/65536 : ℝ) (791740681329/1000000000000 : ℝ) (1027455662231/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0248; no trusted numerical premise.
theorem cover8_leaf0248_exp_radius : (199607590857552481/200000000000000000 : ℝ) ≤ Real.exp ((-16475/1048576 : ℝ)/8) ∧ Real.exp ((-16475/1048576 : ℝ)/8) ≤ (499018977143881203/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16475/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0248_exp_lower : (57507124153459839/62500000000000000 : ℝ) ≤ Real.exp ((-426279517659/640000000000 : ℝ)/8) ∧ Real.exp ((-426279517659/640000000000 : ℝ)/8) ≤ (36804559458214297/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426279517659/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0248_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982231551/200000000000 : ℝ) ≤ 4*Real.exp (8237/65536 : ℝ)*Real.exp (-mu (radius 8 (16475/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410982231551/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16475/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0248_exp_radius
  have hrNumeric : (123051375227/125000000000 : ℝ) ≤ Real.exp (-16475/1048576 : ℝ) ∧ Real.exp (-16475/1048576 : ℝ) ≤ (984411001817/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123051375227/125000000000 : ℝ) ≤ (radius 8 (16475/131072 : ℝ)) ∧ (radius 8 (16475/131072 : ℝ)) ≤ (984411001817/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16475/131072 : ℝ)) (123051375227/125000000000 : ℝ) (984411001817/1000000000000 : ℝ) (87941712943/500000000000 : ℝ) (175883425893/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16475/131072 : ℝ)) (123051375227/125000000000 : ℝ) (984411001817/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123051375227/125000000000 : ℝ) (984411001817/1000000000000 : ℝ) (248051375227/250000000000 : ℝ) (992205500909/1000000000000 : ℝ) (992174884693/1000000000000 : ℝ) (496087442347/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 1 (248051375227/250000000000 : ℝ) (992205500909/1000000000000 : ℝ) (992174884693/1000000000000 : ℝ) (496087442347/500000000000 : ℝ) (1240237741/1250000000 : ℝ) (496095096401/500000000000 : ℝ) (496095096341/500000000000 : ℝ) (248047548171/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 2 (1240237741/1250000000 : ℝ) (496095096401/500000000000 : ℝ) (496095096341/500000000000 : ℝ) (248047548171/250000000000 : ℝ) (992190192741/1000000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 3 (992190192741/1000000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 4 (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 5 (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 6 (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16475/131072 : ℝ)) 7 (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16475/131072 : ℝ))) (87941712943/500000000000 : ℝ) (175883425893/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87941712943/500000000000 : ℝ) (175883425893/1000000000000 : ℝ) (587941712943/1000000000000 : ℝ) (587941712947/1000000000000 : ℝ) (419384579933/1000000000000 : ℝ) (209692289971/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 1 (587941712943/1000000000000 : ℝ) (587941712947/1000000000000 : ℝ) (419384579933/1000000000000 : ℝ) (209692289971/500000000000 : ℝ) (251831573219/500000000000 : ℝ) (100732629289/200000000000 : ℝ) (15517558361/31250000000 : ℝ) (12414046689/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 2 (251831573219/500000000000 : ℝ) (100732629289/200000000000 : ℝ) (15517558361/31250000000 : ℝ) (12414046689/25000000000 : ℝ) (100022501399/200000000000 : ℝ) (500112507003/1000000000000 : ℝ) (500099902631/1000000000000 : ℝ) (6251248783/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 3 (100022501399/200000000000 : ℝ) (500112507003/1000000000000 : ℝ) (500099902631/1000000000000 : ℝ) (6251248783/12500000000 : ℝ) (500106204813/1000000000000 : ℝ) (250053102411/500000000000 : ℝ) (500106204773/1000000000000 : ℝ) (250053102391/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 4 (500106204813/1000000000000 : ℝ) (250053102411/500000000000 : ℝ) (500106204773/1000000000000 : ℝ) (250053102391/500000000000 : ℝ) (500106204793/1000000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 5 (500106204793/1000000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 6 (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16475/131072 : ℝ))) 7 (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16475/131072 : ℝ)) hmem 8 (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16475/131072 : ℝ))) hcmem 8 (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16475/131072 : ℝ)) (49609509637/50000000000 : ℝ) (992190192743/1000000000000 : ℝ) (62513275599/125000000000 : ℝ) (250053102401/500000000000 : ℝ) (79174839183/100000000000 : ℝ) (15834967837/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0248_exp_lower
  have heNumeric : (410982231551/200000000000 : ℝ)/4 ≤ Real.exp (-426279517659/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982231551/200000000000 : ℝ)/4 ≤ Real.exp ((8237/65536 : ℝ)-(15834967837/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8237/65536 : ℝ) (16475/131072 : ℝ) (15834967837/20000000000 : ℝ) (410982231551/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0249; no trusted numerical premise.
theorem cover8_leaf0249_exp_radius : (998037835312374021/1000000000000000000 : ℝ) ≤ Real.exp ((-4119/262144 : ℝ)/8) ∧ Real.exp ((-4119/262144 : ℝ)/8) ≤ (499018917656187011/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4119/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0249_exp_lower : (184022795432269439/200000000000000000 : ℝ) ≤ Real.exp ((-21313978468789/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313978468789/32000000000000 : ℝ)/8) ≤ (230028494290336799/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313978468789/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0249_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455495851/500000000000 : ℝ) ≤ 4*Real.exp (16475/131072 : ℝ)*Real.exp (-mu (radius 8 (4119/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455495851/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4119/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0249_exp_radius
  have hrNumeric : (984410063009/1000000000000 : ℝ) ≤ Real.exp (-4119/262144 : ℝ) ∧ Real.exp (-4119/262144 : ℝ) ≤ (98441006301/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984410063009/1000000000000 : ℝ) ≤ (radius 8 (4119/32768 : ℝ)) ∧ (radius 8 (4119/32768 : ℝ)) ≤ (98441006301/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4119/32768 : ℝ)) (984410063009/1000000000000 : ℝ) (98441006301/100000000000 : ℝ) (87944340131/500000000000 : ℝ) (175888680269/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4119/32768 : ℝ)) (984410063009/1000000000000 : ℝ) (98441006301/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984410063009/1000000000000 : ℝ) (98441006301/100000000000 : ℝ) (62012814469/62500000000 : ℝ) (198441006301/200000000000 : ℝ) (992174411587/1000000000000 : ℝ) (992174411589/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 1 (62012814469/62500000000 : ℝ) (198441006301/200000000000 : ℝ) (992174411587/1000000000000 : ℝ) (992174411589/1000000000000 : ℝ) (198437944309/200000000000 : ℝ) (992189721547/1000000000000 : ℝ) (992189721427/1000000000000 : ℝ) (992189721429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 2 (198437944309/200000000000 : ℝ) (992189721547/1000000000000 : ℝ) (992189721427/1000000000000 : ℝ) (992189721429/1000000000000 : ℝ) (496094860743/500000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 3 (496094860743/500000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 4 (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 5 (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 6 (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4119/32768 : ℝ)) 7 (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4119/32768 : ℝ))) (87944340131/500000000000 : ℝ) (175888680269/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87944340131/500000000000 : ℝ) (175888680269/1000000000000 : ℝ) (587944340131/1000000000000 : ℝ) (117588868027/200000000000 : ℝ) (16775633771/40000000000 : ℝ) (104847711071/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 1 (587944340131/1000000000000 : ℝ) (117588868027/200000000000 : ℝ) (16775633771/40000000000 : ℝ) (104847711071/250000000000 : ℝ) (503667592203/1000000000000 : ℝ) (50366759221/100000000000 : ℝ) (248283342773/500000000000 : ℝ) (248283342777/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 2 (503667592203/1000000000000 : ℝ) (50366759221/100000000000 : ℝ) (248283342773/500000000000 : ℝ) (248283342777/500000000000 : ℝ) (250058569437/500000000000 : ℝ) (250058569441/500000000000 : ℝ) (500104535949/1000000000000 : ℝ) (500104535957/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 3 (250058569437/500000000000 : ℝ) (250058569441/500000000000 : ℝ) (500104535949/1000000000000 : ℝ) (500104535957/1000000000000 : ℝ) (500110837411/1000000000000 : ℝ) (25005541871/50000000000 : ℝ) (500110837371/1000000000000 : ℝ) (25005541869/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 4 (500110837411/1000000000000 : ℝ) (25005541871/50000000000 : ℝ) (500110837371/1000000000000 : ℝ) (25005541869/50000000000 : ℝ) (500110837391/1000000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 5 (500110837391/1000000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 6 (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4119/32768 : ℝ))) 7 (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4119/32768 : ℝ)) hmem 8 (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4119/32768 : ℝ))) hcmem 8 (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4119/32768 : ℝ)) (198437944297/200000000000 : ℝ) (62011857593/62500000000 : ℝ) (50011083739/100000000000 : ℝ) (2500554187/5000000000 : ℝ) (49484756377/62500000000 : ℝ) (197939025513/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0249_exp_lower
  have heNumeric : (1027455495851/500000000000 : ℝ)/4 ≤ Real.exp (-21313978468789/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455495851/500000000000 : ℝ)/4 ≤ Real.exp ((16475/131072 : ℝ)-(197939025513/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16475/131072 : ℝ) (4119/32768 : ℝ) (197939025513/250000000000 : ℝ) (1027455495851/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0225_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0225_certificate
#check SmaleRate.Proofs.cover8_leaf0226_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0226_certificate
#check SmaleRate.Proofs.cover8_leaf0227_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0227_certificate
#check SmaleRate.Proofs.cover8_leaf0228_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0228_certificate
#check SmaleRate.Proofs.cover8_leaf0229_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0229_certificate
#check SmaleRate.Proofs.cover8_leaf0230_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0230_certificate
#check SmaleRate.Proofs.cover8_leaf0231_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0231_certificate
#check SmaleRate.Proofs.cover8_leaf0232_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0232_certificate
#check SmaleRate.Proofs.cover8_leaf0233_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0233_certificate
#check SmaleRate.Proofs.cover8_leaf0234_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0234_certificate
#check SmaleRate.Proofs.cover8_leaf0235_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0235_certificate
#check SmaleRate.Proofs.cover8_leaf0236_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0236_certificate
#check SmaleRate.Proofs.cover8_leaf0237_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0237_certificate
#check SmaleRate.Proofs.cover8_leaf0238_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0238_certificate
#check SmaleRate.Proofs.cover8_leaf0239_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0239_certificate
#check SmaleRate.Proofs.cover8_leaf0240_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0240_certificate
#check SmaleRate.Proofs.cover8_leaf0241_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0241_certificate
#check SmaleRate.Proofs.cover8_leaf0242_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0242_certificate
#check SmaleRate.Proofs.cover8_leaf0243_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0243_certificate
#check SmaleRate.Proofs.cover8_leaf0244_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0244_certificate
#check SmaleRate.Proofs.cover8_leaf0245_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0245_certificate
#check SmaleRate.Proofs.cover8_leaf0246_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0246_certificate
#check SmaleRate.Proofs.cover8_leaf0247_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0247_certificate
#check SmaleRate.Proofs.cover8_leaf0248_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0248_certificate
#check SmaleRate.Proofs.cover8_leaf0249_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0249_certificate
