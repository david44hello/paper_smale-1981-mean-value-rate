/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1375; no trusted numerical premise.
theorem cover8_leaf1375_exp_radius : (997986915148205437/1000000000000000000 : ℝ) ≤ Real.exp ((-2113/131072 : ℝ)/8) ∧ Real.exp ((-2113/131072 : ℝ)/8) ≤ (498993457574102719/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2113/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1375_exp_lower : (18402274875649523/20000000000000000 : ℝ) ≤ Real.exp ((-42628086801921/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628086801921/64000000000000 : ℝ)/8) ≤ (920113743782476151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628086801921/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1375_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863352753/125000000000 : ℝ) ≤ 4*Real.exp (33807/262144 : ℝ)*Real.exp (-mu (radius 8 (2113/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (256863352753/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2113/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1375_exp_radius
  have hrNumeric : (49200416789/50000000000 : ℝ) ≤ Real.exp (-2113/131072 : ℝ) ∧ Real.exp (-2113/131072 : ℝ) ≤ (984008335781/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49200416789/50000000000 : ℝ) ≤ (radius 8 (2113/16384 : ℝ)) ∧ (radius 8 (2113/16384 : ℝ)) ≤ (984008335781/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2113/16384 : ℝ)) (49200416789/50000000000 : ℝ) (984008335781/1000000000000 : ℝ) (178122416089/1000000000000 : ℝ) (35624483219/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2113/16384 : ℝ)) (49200416789/50000000000 : ℝ) (984008335781/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49200416789/50000000000 : ℝ) (984008335781/1000000000000 : ℝ) (99200416789/100000000000 : ℝ) (992004167891/1000000000000 : ℝ) (1549956161/1562500000 : ℝ) (495985971521/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 1 (99200416789/100000000000 : ℝ) (992004167891/1000000000000 : ℝ) (1549956161/1562500000 : ℝ) (495985971521/500000000000 : ℝ) (198397611093/200000000000 : ℝ) (991988055467/1000000000000 : ℝ) (495994027667/500000000000 : ℝ) (123998506917/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 2 (198397611093/200000000000 : ℝ) (991988055467/1000000000000 : ℝ) (495994027667/500000000000 : ℝ) (123998506917/125000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 3 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 4 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 5 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 6 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2113/16384 : ℝ)) 7 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2113/16384 : ℝ))) (178122416089/1000000000000 : ℝ) (35624483219/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178122416089/1000000000000 : ℝ) (35624483219/200000000000 : ℝ) (147265302011/250000000000 : ℝ) (36816325503/62500000000 : ℝ) (211022757119/500000000000 : ℝ) (211022757123/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 1 (147265302011/250000000000 : ℝ) (36816325503/62500000000 : ℝ) (211022757119/500000000000 : ℝ) (211022757123/500000000000 : ℝ) (505553361141/1000000000000 : ℝ) (505553361147/1000000000000 : ℝ) (124652176191/250000000000 : ℝ) (498608704771/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 2 (505553361141/1000000000000 : ℝ) (505553361147/1000000000000 : ℝ) (124652176191/250000000000 : ℝ) (498608704771/1000000000000 : ℝ) (62760129119/125000000000 : ℝ) (502081032959/1000000000000 : ℝ) (12551725643/25000000000 : ℝ) (502069025727/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 3 (62760129119/125000000000 : ℝ) (502081032959/1000000000000 : ℝ) (12551725643/25000000000 : ℝ) (502069025727/1000000000000 : ℝ) (62759378667/125000000000 : ℝ) (502075029343/1000000000000 : ℝ) (5020750293/10000000000 : ℝ) (125518757327/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 4 (62759378667/125000000000 : ℝ) (502075029343/1000000000000 : ℝ) (5020750293/10000000000 : ℝ) (125518757327/250000000000 : ℝ) (251037514659/500000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 5 (251037514659/500000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 6 (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2113/16384 : ℝ))) 7 (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2113/16384 : ℝ)) hmem 8 (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2113/16384 : ℝ))) hcmem 8 (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2113/16384 : ℝ)) (991988055399/1000000000000 : ℝ) (495994027701/500000000000 : ℝ) (502075029317/1000000000000 : ℝ) (251037514663/500000000000 : ℝ) (397513663361/500000000000 : ℝ) (795027326739/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1375_exp_lower
  have heNumeric : (256863352753/125000000000 : ℝ)/4 ≤ Real.exp (-42628086801921/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863352753/125000000000 : ℝ)/4 ≤ Real.exp ((33807/262144 : ℝ)-(795027326739/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33807/262144 : ℝ) (2113/16384 : ℝ) (795027326739/1000000000000 : ℝ) (256863352753/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1376; no trusted numerical premise.
theorem cover8_leaf1376_exp_radius : (498993427831775821/500000000000000000 : ℝ) ≤ Real.exp ((-33809/2097152 : ℝ)/8) ∧ Real.exp ((-33809/2097152 : ℝ)/8) ≤ (997986855663551643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33809/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1376_exp_lower : (920113746796454287/1000000000000000000 : ℝ) ≤ Real.exp ((-2664255320299/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664255320299/4000000000000 : ℝ)/8) ≤ (57507109174778393/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664255320299/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1376_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453437937/500000000000 : ℝ) ≤ 4*Real.exp (2113/16384 : ℝ)*Real.exp (-mu (radius 8 (33809/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453437937/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33809/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1376_exp_radius
  have hrNumeric : (123000983321/125000000000 : ℝ) ≤ Real.exp (-33809/2097152 : ℝ) ∧ Real.exp (-33809/2097152 : ℝ) ≤ (984007866569/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123000983321/125000000000 : ℝ) ≤ (radius 8 (33809/262144 : ℝ)) ∧ (radius 8 (33809/262144 : ℝ)) ≤ (984007866569/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33809/262144 : ℝ)) (123000983321/125000000000 : ℝ) (984007866569/1000000000000 : ℝ) (35625001631/200000000000 : ℝ) (178125008161/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33809/262144 : ℝ)) (123000983321/125000000000 : ℝ) (984007866569/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123000983321/125000000000 : ℝ) (984007866569/1000000000000 : ℝ) (248000983321/250000000000 : ℝ) (198400786657/200000000000 : ℝ) (123996463317/125000000000 : ℝ) (991971706537/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 1 (248000983321/250000000000 : ℝ) (198400786657/200000000000 : ℝ) (123996463317/125000000000 : ℝ) (991971706537/1000000000000 : ℝ) (99198781991/100000000000 : ℝ) (991987819911/1000000000000 : ℝ) (991987819779/1000000000000 : ℝ) (991987819781/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 2 (99198781991/100000000000 : ℝ) (991987819911/1000000000000 : ℝ) (991987819779/1000000000000 : ℝ) (991987819781/1000000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 3 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 4 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 5 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 6 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33809/262144 : ℝ)) 7 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33809/262144 : ℝ))) (35625001631/200000000000 : ℝ) (178125008161/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35625001631/200000000000 : ℝ) (178125008161/1000000000000 : ℝ) (589062504077/1000000000000 : ℝ) (589062504081/1000000000000 : ℝ) (52756073133/125000000000 : ℝ) (26378036567/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 1 (589062504077/1000000000000 : ℝ) (589062504081/1000000000000 : ℝ) (52756073133/125000000000 : ℝ) (26378036567/62500000000 : ℝ) (50555554457/100000000000 : ℝ) (505555544577/1000000000000 : ℝ) (19944442689/40000000000 : ℝ) (498611067233/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 2 (50555554457/100000000000 : ℝ) (505555544577/1000000000000 : ℝ) (19944442689/40000000000 : ℝ) (498611067233/1000000000000 : ℝ) (502083305897/1000000000000 : ℝ) (100416661181/200000000000 : ℝ) (251035649669/500000000000 : ℝ) (502071299347/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 3 (502083305897/1000000000000 : ℝ) (100416661181/200000000000 : ℝ) (251035649669/500000000000 : ℝ) (502071299347/1000000000000 : ℝ) (502077302617/1000000000000 : ℝ) (251038651313/500000000000 : ℝ) (502077302581/1000000000000 : ℝ) (502077302591/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 4 (502077302617/1000000000000 : ℝ) (251038651313/500000000000 : ℝ) (502077302581/1000000000000 : ℝ) (502077302591/1000000000000 : ℝ) (502077302599/1000000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 5 (502077302599/1000000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 6 (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33809/262144 : ℝ))) 7 (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33809/262144 : ℝ)) hmem 8 (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33809/262144 : ℝ))) hcmem 8 (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33809/262144 : ℝ)) (247996954961/250000000000 : ℝ) (495993909923/500000000000 : ℝ) (251038651299/500000000000 : ℝ) (502077302609/1000000000000 : ℝ) (795031115211/1000000000000 : ℝ) (795031115231/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1376_exp_lower
  have heNumeric : (1027453437937/500000000000 : ℝ)/4 ≤ Real.exp (-2664255320299/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453437937/500000000000 : ℝ)/4 ≤ Real.exp ((2113/16384 : ℝ)-(795031115231/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2113/16384 : ℝ) (33809/262144 : ℝ) (795031115231/1000000000000 : ℝ) (1027453437937/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1377; no trusted numerical premise.
theorem cover8_leaf1377_exp_radius : (62374174761181337/62500000000000000 : ℝ) ≤ Real.exp ((-16905/1048576 : ℝ)/8) ∧ Real.exp ((-16905/1048576 : ℝ)/8) ≤ (997986796178901393/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16905/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1377_exp_lower : (920113749820093629/1000000000000000000 : ℝ) ≤ Real.exp ((-42628083442271/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628083442271/64000000000000 : ℝ)/8) ≤ (92011374982009363/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628083442271/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1377_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863366237/125000000000 : ℝ) ≤ 4*Real.exp (33809/262144 : ℝ)*Real.exp (-mu (radius 8 (16905/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256863366237/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16905/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1377_exp_radius
  have hrNumeric : (984007397357/1000000000000 : ℝ) ≤ Real.exp (-16905/1048576 : ℝ) ∧ Real.exp (-16905/1048576 : ℝ) ≤ (492003698679/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984007397357/1000000000000 : ℝ) ≤ (radius 8 (16905/131072 : ℝ)) ∧ (radius 8 (16905/131072 : ℝ)) ≤ (492003698679/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16905/131072 : ℝ)) (984007397357/1000000000000 : ℝ) (492003698679/500000000000 : ℝ) (11132975011/62500000000 : ℝ) (178127600183/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16905/131072 : ℝ)) (984007397357/1000000000000 : ℝ) (492003698679/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984007397357/1000000000000 : ℝ) (492003698679/500000000000 : ℝ) (496001849339/500000000000 : ℝ) (992003698679/1000000000000 : ℝ) (991971470031/1000000000000 : ℝ) (991971470033/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 1 (496001849339/500000000000 : ℝ) (992003698679/1000000000000 : ℝ) (991971470031/1000000000000 : ℝ) (991971470033/1000000000000 : ℝ) (495993792177/500000000000 : ℝ) (247996896089/250000000000 : ℝ) (991987584223/1000000000000 : ℝ) (495993792113/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 2 (495993792177/500000000000 : ℝ) (247996896089/250000000000 : ℝ) (991987584223/1000000000000 : ℝ) (495993792113/500000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 3 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 4 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 5 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 6 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16905/131072 : ℝ)) 7 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16905/131072 : ℝ))) (11132975011/62500000000 : ℝ) (178127600183/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11132975011/62500000000 : ℝ) (178127600183/1000000000000 : ℝ) (73632975011/125000000000 : ℝ) (147265950023/250000000000 : ℝ) (211025827907/500000000000 : ℝ) (26378228489/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 1 (73632975011/125000000000 : ℝ) (147265950023/250000000000 : ℝ) (211025827907/500000000000 : ℝ) (26378228489/62500000000 : ℝ) (505557727951/1000000000000 : ℝ) (252778863979/500000000000 : ℝ) (498613429629/1000000000000 : ℝ) (249306714819/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 2 (505557727951/1000000000000 : ℝ) (252778863979/500000000000 : ℝ) (498613429629/1000000000000 : ℝ) (249306714819/500000000000 : ℝ) (50208557879/100000000000 : ℝ) (251042789399/500000000000 : ℝ) (62759196613/125000000000 : ℝ) (502073572913/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 3 (50208557879/100000000000 : ℝ) (251042789399/500000000000 : ℝ) (62759196613/125000000000 : ℝ) (502073572913/1000000000000 : ℝ) (502079575847/1000000000000 : ℝ) (31379973491/62500000000 : ℝ) (502079575811/1000000000000 : ℝ) (25103978791/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 4 (502079575847/1000000000000 : ℝ) (31379973491/62500000000 : ℝ) (502079575811/1000000000000 : ℝ) (25103978791/50000000000 : ℝ) (502079575829/1000000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 5 (502079575829/1000000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 6 (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16905/131072 : ℝ))) 7 (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16905/131072 : ℝ)) hmem 8 (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16905/131072 : ℝ))) hcmem 8 (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16905/131072 : ℝ)) (30999612009/31250000000 : ℝ) (991987584291/1000000000000 : ℝ) (125519893957/250000000000 : ℝ) (251039787919/500000000000 : ℝ) (39751745181/50000000000 : ℝ) (795034903639/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1377_exp_lower
  have heNumeric : (256863366237/125000000000 : ℝ)/4 ≤ Real.exp (-42628083442271/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863366237/125000000000 : ℝ)/4 ≤ Real.exp ((33809/262144 : ℝ)-(795034903639/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33809/262144 : ℝ) (16905/131072 : ℝ) (795034903639/1000000000000 : ℝ) (256863366237/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1378; no trusted numerical premise.
theorem cover8_leaf1378_exp_radius : (31187085521695459/31250000000000000 : ℝ) ≤ Real.exp ((-33811/2097152 : ℝ)/8) ∧ Real.exp ((-33811/2097152 : ℝ)/8) ≤ (997986736694254689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33811/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1378_exp_lower : (920113752851438933/1000000000000000000 : ℝ) ≤ Real.exp ((-4262808175547/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262808175547/6400000000000 : ℝ)/8) ≤ (460056876425719467/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262808175547/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1378_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981396811/200000000000 : ℝ) ≤ 4*Real.exp (16905/131072 : ℝ)*Real.exp (-mu (radius 8 (33811/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410981396811/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33811/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1378_exp_radius
  have hrNumeric : (196801385629/200000000000 : ℝ) ≤ Real.exp (-33811/2097152 : ℝ) ∧ Real.exp (-33811/2097152 : ℝ) ≤ (492003464073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196801385629/200000000000 : ℝ) ≤ (radius 8 (33811/262144 : ℝ)) ∧ (radius 8 (33811/262144 : ℝ)) ≤ (492003464073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33811/262144 : ℝ)) (196801385629/200000000000 : ℝ) (492003464073/500000000000 : ℝ) (44532548041/250000000000 : ℝ) (178130192171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33811/262144 : ℝ)) (196801385629/200000000000 : ℝ) (492003464073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196801385629/200000000000 : ℝ) (492003464073/500000000000 : ℝ) (124000433009/125000000000 : ℝ) (992003464073/1000000000000 : ℝ) (495985616763/500000000000 : ℝ) (123996404191/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 1 (124000433009/125000000000 : ℝ) (992003464073/1000000000000 : ℝ) (495985616763/500000000000 : ℝ) (123996404191/125000000000 : ℝ) (991987348799/1000000000000 : ℝ) (991987348801/1000000000000 : ℝ) (247996837167/250000000000 : ℝ) (99198734867/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 2 (991987348799/1000000000000 : ℝ) (991987348801/1000000000000 : ℝ) (247996837167/250000000000 : ℝ) (99198734867/100000000000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 3 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 4 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 5 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 6 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33811/262144 : ℝ)) 7 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33811/262144 : ℝ))) (44532548041/250000000000 : ℝ) (178130192171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44532548041/250000000000 : ℝ) (178130192171/1000000000000 : ℝ) (294532548041/500000000000 : ℝ) (294532548043/500000000000 : ℝ) (422054726503/1000000000000 : ℝ) (26378420407/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 1 (294532548041/500000000000 : ℝ) (294532548043/500000000000 : ℝ) (422054726503/1000000000000 : ℝ) (26378420407/62500000000 : ℝ) (126389977823/250000000000 : ℝ) (505559911299/1000000000000 : ℝ) (498615791987/1000000000000 : ℝ) (99723158399/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 2 (126389977823/250000000000 : ℝ) (505559911299/1000000000000 : ℝ) (498615791987/1000000000000 : ℝ) (99723158399/200000000000 : ℝ) (502087851639/1000000000000 : ℝ) (502087851647/1000000000000 : ℝ) (502075846427/1000000000000 : ℝ) (100415169287/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 3 (502087851639/1000000000000 : ℝ) (502087851647/1000000000000 : ℝ) (502075846427/1000000000000 : ℝ) (100415169287/200000000000 : ℝ) (502081849033/1000000000000 : ℝ) (502081849041/1000000000000 : ℝ) (502081848997/1000000000000 : ℝ) (251040924503/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 4 (502081849033/1000000000000 : ℝ) (502081849041/1000000000000 : ℝ) (502081848997/1000000000000 : ℝ) (251040924503/500000000000 : ℝ) (100416369803/200000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 5 (100416369803/200000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 6 (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33811/262144 : ℝ))) 7 (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33811/262144 : ℝ)) hmem 8 (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33811/262144 : ℝ))) hcmem 8 (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33811/262144 : ℝ)) (991987348733/1000000000000 : ℝ) (3874950581/3906250000 : ℝ) (251040924507/500000000000 : ℝ) (7845028891/15625000000 : ℝ) (795038691961/1000000000000 : ℝ) (39751934599/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1378_exp_lower
  have heNumeric : (410981396811/200000000000 : ℝ)/4 ≤ Real.exp (-4262808175547/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981396811/200000000000 : ℝ)/4 ≤ Real.exp ((16905/131072 : ℝ)-(39751934599/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16905/131072 : ℝ) (33811/262144 : ℝ) (39751934599/50000000000 : ℝ) (410981396811/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1379; no trusted numerical premise.
theorem cover8_leaf1379_exp_radius : (99798667720961153/100000000000000000 : ℝ) ≤ Real.exp ((-8453/524288 : ℝ)/8) ∧ Real.exp ((-8453/524288 : ℝ)/8) ≤ (997986677209611531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8453/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1379_exp_lower : (2300284389730251/2500000000000000 : ℝ) ≤ Real.exp ((-8525616012697/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525616012697/12800000000000 : ℝ)/8) ≤ (920113755892100401/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525616012697/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1379_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453519191/500000000000 : ℝ) ≤ 4*Real.exp (33811/262144 : ℝ)*Real.exp (-mu (radius 8 (8453/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453519191/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8453/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1379_exp_radius
  have hrNumeric : (492003229467/500000000000 : ℝ) ≤ Real.exp (-8453/524288 : ℝ) ∧ Real.exp (-8453/524288 : ℝ) ≤ (196801291787/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492003229467/500000000000 : ℝ) ≤ (radius 8 (8453/65536 : ℝ)) ∧ (radius 8 (8453/65536 : ℝ)) ≤ (196801291787/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8453/65536 : ℝ)) (492003229467/500000000000 : ℝ) (196801291787/200000000000 : ℝ) (44533196027/250000000000 : ℝ) (89066392057/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8453/65536 : ℝ)) (492003229467/500000000000 : ℝ) (196801291787/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492003229467/500000000000 : ℝ) (196801291787/200000000000 : ℝ) (992003229467/1000000000000 : ℝ) (248000807367/250000000000 : ℝ) (495985498511/500000000000 : ℝ) (30999093657/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 1 (992003229467/1000000000000 : ℝ) (248000807367/250000000000 : ℝ) (495985498511/500000000000 : ℝ) (30999093657/31250000000 : ℝ) (247996778311/250000000000 : ℝ) (495993556623/500000000000 : ℝ) (991987113113/1000000000000 : ℝ) (247996778279/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 2 (247996778311/250000000000 : ℝ) (495993556623/500000000000 : ℝ) (991987113113/1000000000000 : ℝ) (247996778279/250000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 3 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 4 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 5 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 6 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8453/65536 : ℝ)) 7 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8453/65536 : ℝ))) (44533196027/250000000000 : ℝ) (89066392057/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44533196027/250000000000 : ℝ) (89066392057/500000000000 : ℝ) (294533196027/500000000000 : ℝ) (589066392057/1000000000000 : ℝ) (422057797117/1000000000000 : ℝ) (3376462377/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 1 (294533196027/500000000000 : ℝ) (589066392057/1000000000000 : ℝ) (422057797117/1000000000000 : ℝ) (3376462377/8000000000 : ℝ) (101112418917/200000000000 : ℝ) (505562094591/1000000000000 : ℝ) (31163634643/62500000000 : ℝ) (99723630859/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 2 (101112418917/200000000000 : ℝ) (505562094591/1000000000000 : ℝ) (31163634643/62500000000 : ℝ) (99723630859/200000000000 : ℝ) (125522531109/250000000000 : ℝ) (502090124443/1000000000000 : ℝ) (502078119897/1000000000000 : ℝ) (100415623981/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 3 (125522531109/250000000000 : ℝ) (502090124443/1000000000000 : ℝ) (502078119897/1000000000000 : ℝ) (100415623981/200000000000 : ℝ) (251042061083/500000000000 : ℝ) (251042061087/500000000000 : ℝ) (50208412213/100000000000 : ℝ) (502084122139/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 4 (251042061083/500000000000 : ℝ) (251042061087/500000000000 : ℝ) (50208412213/100000000000 : ℝ) (502084122139/1000000000000 : ℝ) (125521030537/250000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 5 (125521030537/250000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 6 (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8453/65536 : ℝ))) 7 (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8453/65536 : ℝ)) hmem 8 (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8453/65536 : ℝ))) hcmem 8 (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8453/65536 : ℝ)) (495993556589/500000000000 : ℝ) (991987113181/1000000000000 : ℝ) (502084122147/1000000000000 : ℝ) (502084122157/1000000000000 : ℝ) (39752124011/50000000000 : ℝ) (9938031003/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1379_exp_lower
  have heNumeric : (1027453519191/500000000000 : ℝ)/4 ≤ Real.exp (-8525616012697/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453519191/500000000000 : ℝ)/4 ≤ Real.exp ((33811/262144 : ℝ)-(9938031003/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33811/262144 : ℝ) (8453/65536 : ℝ) (9938031003/12500000000 : ℝ) (1027453519191/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1380; no trusted numerical premise.
theorem cover8_leaf1380_exp_radius : (997986617724971917/1000000000000000000 : ℝ) ≤ Real.exp ((-33813/2097152 : ℝ)/8) ∧ Real.exp ((-33813/2097152 : ℝ)/8) ≤ (498993308862485959/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33813/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1380_exp_lower : (115014219867788507/125000000000000000 : ℝ) ≤ Real.exp ((-10657019591547/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657019591547/16000000000000 : ℝ)/8) ≤ (920113758942308057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657019591547/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1380_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453546439/500000000000 : ℝ) ≤ 4*Real.exp (8453/65536 : ℝ)*Real.exp (-mu (radius 8 (33813/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453546439/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33813/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1380_exp_radius
  have hrNumeric : (246001497431/250000000000 : ℝ) ≤ Real.exp (-33813/2097152 : ℝ) ∧ Real.exp (-33813/2097152 : ℝ) ≤ (39360239589/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246001497431/250000000000 : ℝ) ≤ (radius 8 (33813/262144 : ℝ)) ∧ (radius 8 (33813/262144 : ℝ)) ≤ (39360239589/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33813/262144 : ℝ)) (246001497431/250000000000 : ℝ) (39360239589/40000000000 : ℝ) (178135376007/1000000000000 : ℝ) (178135376013/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33813/262144 : ℝ)) (246001497431/250000000000 : ℝ) (39360239589/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246001497431/250000000000 : ℝ) (39360239589/40000000000 : ℝ) (496001497431/500000000000 : ℝ) (992002994863/1000000000000 : ℝ) (495985380259/500000000000 : ℝ) (24799269013/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 1 (496001497431/500000000000 : ℝ) (992002994863/1000000000000 : ℝ) (495985380259/500000000000 : ℝ) (24799269013/25000000000 : ℝ) (99198687769/100000000000 : ℝ) (247996719423/250000000000 : ℝ) (991986877559/1000000000000 : ℝ) (991986877561/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 2 (99198687769/100000000000 : ℝ) (247996719423/250000000000 : ℝ) (991986877559/1000000000000 : ℝ) (991986877561/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 3 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 4 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 5 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 6 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33813/262144 : ℝ)) 7 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33813/262144 : ℝ))) (178135376007/1000000000000 : ℝ) (178135376013/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178135376007/1000000000000 : ℝ) (178135376013/1000000000000 : ℝ) (589067688003/1000000000000 : ℝ) (589067688007/1000000000000 : ℝ) (52757608457/125000000000 : ℝ) (26378804229/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 1 (589067688003/1000000000000 : ℝ) (589067688007/1000000000000 : ℝ) (52757608457/125000000000 : ℝ) (26378804229/62500000000 : ℝ) (505564277829/1000000000000 : ℝ) (126391069459/250000000000 : ℝ) (124655129133/250000000000 : ℝ) (498620516539/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 2 (505564277829/1000000000000 : ℝ) (126391069459/250000000000 : ℝ) (124655129133/250000000000 : ℝ) (498620516539/1000000000000 : ℝ) (25104619859/50000000000 : ℝ) (125523099297/250000000000 : ℝ) (251040196657/500000000000 : ℝ) (251040196661/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 3 (25104619859/50000000000 : ℝ) (125523099297/250000000000 : ℝ) (251040196657/500000000000 : ℝ) (251040196661/500000000000 : ℝ) (502086395247/1000000000000 : ℝ) (100417279051/200000000000 : ℝ) (502086395211/1000000000000 : ℝ) (25104319761/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 4 (502086395247/1000000000000 : ℝ) (100417279051/200000000000 : ℝ) (502086395211/1000000000000 : ℝ) (25104319761/50000000000 : ℝ) (502086395229/1000000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 5 (502086395229/1000000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 6 (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33813/262144 : ℝ))) 7 (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33813/262144 : ℝ)) hmem 8 (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33813/262144 : ℝ))) hcmem 8 (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33813/262144 : ℝ)) (123998359703/125000000000 : ℝ) (991986877627/1000000000000 : ℝ) (125521598807/250000000000 : ℝ) (251043197619/500000000000 : ℝ) (397523134199/500000000000 : ℝ) (795046268417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1380_exp_lower
  have heNumeric : (1027453546439/500000000000 : ℝ)/4 ≤ Real.exp (-10657019591547/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453546439/500000000000 : ℝ)/4 ≤ Real.exp ((8453/65536 : ℝ)-(795046268417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8453/65536 : ℝ) (33813/262144 : ℝ) (795046268417/1000000000000 : ℝ) (1027453546439/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1381; no trusted numerical premise.
theorem cover8_leaf1381_exp_radius : (997986558240335849/1000000000000000000 : ℝ) ≤ Real.exp ((-16907/1048576 : ℝ)/8) ∧ Real.exp ((-16907/1048576 : ℝ)/8) ≤ (19959731164806717/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16907/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1381_exp_lower : (920113761999876633/1000000000000000000 : ℝ) ≤ Real.exp ((-8525615332959/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525615332959/12800000000000 : ℝ)/8) ≤ (460056880999938317/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525615332959/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1381_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453573753/500000000000 : ℝ) ≤ 4*Real.exp (33813/262144 : ℝ)*Real.exp (-mu (radius 8 (16907/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453573753/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16907/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1381_exp_radius
  have hrNumeric : (984005520513/1000000000000 : ℝ) ≤ Real.exp (-16907/1048576 : ℝ) ∧ Real.exp (-16907/1048576 : ℝ) ≤ (492002760257/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984005520513/1000000000000 : ℝ) ≤ (radius 8 (16907/131072 : ℝ)) ∧ (radius 8 (16907/131072 : ℝ)) ≤ (492002760257/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16907/131072 : ℝ)) (984005520513/1000000000000 : ℝ) (492002760257/500000000000 : ℝ) (178137967873/1000000000000 : ℝ) (178137967879/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16907/131072 : ℝ)) (984005520513/1000000000000 : ℝ) (492002760257/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984005520513/1000000000000 : ℝ) (492002760257/500000000000 : ℝ) (15500043129/15625000000 : ℝ) (992002760257/1000000000000 : ℝ) (495985262007/500000000000 : ℝ) (198394104803/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 1 (15500043129/15625000000 : ℝ) (992002760257/1000000000000 : ℝ) (495985262007/500000000000 : ℝ) (198394104803/200000000000 : ℝ) (198397328427/200000000000 : ℝ) (123998330267/125000000000 : ℝ) (247996660501/250000000000 : ℝ) (495993321003/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 2 (198397328427/200000000000 : ℝ) (123998330267/125000000000 : ℝ) (247996660501/250000000000 : ℝ) (495993321003/500000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 3 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 4 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 5 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 6 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16907/131072 : ℝ)) 7 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16907/131072 : ℝ))) (178137967873/1000000000000 : ℝ) (178137967879/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178137967873/1000000000000 : ℝ) (178137967879/1000000000000 : ℝ) (4602101437/7812500000 : ℝ) (29453449197/50000000000 : ℝ) (422063938133/1000000000000 : ℝ) (422063938141/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 1 (4602101437/7812500000 : ℝ) (29453449197/50000000000 : ℝ) (422063938133/1000000000000 : ℝ) (422063938141/1000000000000 : ℝ) (252783230517/500000000000 : ℝ) (505566461041/1000000000000 : ℝ) (498622878729/1000000000000 : ℝ) (31163929921/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 2 (252783230517/500000000000 : ℝ) (505566461041/1000000000000 : ℝ) (498622878729/1000000000000 : ℝ) (31163929921/62500000000 : ℝ) (502094669881/1000000000000 : ℝ) (502094669889/1000000000000 : ℝ) (502082666689/1000000000000 : ℝ) (502082666697/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 3 (502094669881/1000000000000 : ℝ) (502094669889/1000000000000 : ℝ) (502082666689/1000000000000 : ℝ) (502082666697/1000000000000 : ℝ) (100417733657/200000000000 : ℝ) (502088668293/1000000000000 : ℝ) (502088668249/1000000000000 : ℝ) (251044334129/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 4 (100417733657/200000000000 : ℝ) (502088668293/1000000000000 : ℝ) (502088668249/1000000000000 : ℝ) (251044334129/500000000000 : ℝ) (502088668267/1000000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 5 (502088668267/1000000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 6 (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16907/131072 : ℝ))) 7 (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16907/131072 : ℝ)) hmem 8 (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16907/131072 : ℝ))) hcmem 8 (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16907/131072 : ℝ)) (991986642069/1000000000000 : ℝ) (991986642071/1000000000000 : ℝ) (251044334133/500000000000 : ℝ) (125522167069/250000000000 : ℝ) (795050056511/1000000000000 : ℝ) (79505005653/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1381_exp_lower
  have heNumeric : (1027453573753/500000000000 : ℝ)/4 ≤ Real.exp (-8525615332959/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453573753/500000000000 : ℝ)/4 ≤ Real.exp ((33813/262144 : ℝ)-(79505005653/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33813/262144 : ℝ) (16907/131072 : ℝ) (79505005653/100000000000 : ℝ) (1027453573753/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1382; no trusted numerical premise.
theorem cover8_leaf1382_exp_radius : (31187078086115729/31250000000000000 : ℝ) ≤ Real.exp ((-33815/2097152 : ℝ)/8) ∧ Real.exp ((-33815/2097152 : ℝ)/8) ≤ (997986498755703329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33815/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1382_exp_lower : (230028441266805357/250000000000000000 : ℝ) ≤ Real.exp ((-21314037478981/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314037478981/32000000000000 : ℝ)/8) ≤ (920113765067221429/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314037478981/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1382_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907202309/1000000000000 : ℝ) ≤ 4*Real.exp (16907/131072 : ℝ)*Real.exp (-mu (radius 8 (33815/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907202309/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33815/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1382_exp_radius
  have hrNumeric : (984005051303/1000000000000 : ℝ) ≤ Real.exp (-33815/2097152 : ℝ) ∧ Real.exp (-33815/2097152 : ℝ) ≤ (123000631413/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984005051303/1000000000000 : ℝ) ≤ (radius 8 (33815/262144 : ℝ)) ∧ (radius 8 (33815/262144 : ℝ)) ≤ (123000631413/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33815/262144 : ℝ)) (984005051303/1000000000000 : ℝ) (123000631413/125000000000 : ℝ) (89070279847/500000000000 : ℝ) (1781405597/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33815/262144 : ℝ)) (984005051303/1000000000000 : ℝ) (123000631413/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984005051303/1000000000000 : ℝ) (123000631413/125000000000 : ℝ) (992002525651/1000000000000 : ℝ) (248000631413/250000000000 : ℝ) (99197028751/100000000000 : ℝ) (991970287511/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 1 (992002525651/1000000000000 : ℝ) (248000631413/250000000000 : ℝ) (99197028751/100000000000 : ℝ) (991970287511/1000000000000 : ℝ) (49599320329/50000000000 : ℝ) (495993203291/500000000000 : ℝ) (991986406449/1000000000000 : ℝ) (991986406451/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 2 (49599320329/50000000000 : ℝ) (495993203291/500000000000 : ℝ) (991986406449/1000000000000 : ℝ) (991986406451/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 3 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 4 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 5 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 6 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33815/262144 : ℝ)) 7 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33815/262144 : ℝ))) (89070279847/500000000000 : ℝ) (1781405597/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89070279847/500000000000 : ℝ) (1781405597/10000000000 : ℝ) (589070279847/1000000000000 : ℝ) (11781405597/20000000000 : ℝ) (84413401707/200000000000 : ℝ) (422067008543/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 1 (589070279847/1000000000000 : ℝ) (11781405597/20000000000 : ℝ) (84413401707/200000000000 : ℝ) (422067008543/1000000000000 : ℝ) (505568644191/1000000000000 : ℝ) (505568644197/1000000000000 : ℝ) (498625240869/1000000000000 : ℝ) (124656310219/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 2 (505568644191/1000000000000 : ℝ) (505568644197/1000000000000 : ℝ) (498625240869/1000000000000 : ℝ) (124656310219/250000000000 : ℝ) (50209694253/100000000000 : ℝ) (502096942537/1000000000000 : ℝ) (50208494001/100000000000 : ℝ) (251042470009/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 3 (50209694253/100000000000 : ℝ) (502096942537/1000000000000 : ℝ) (50208494001/100000000000 : ℝ) (251042470009/500000000000 : ℝ) (50209094127/100000000000 : ℝ) (251045470639/500000000000 : ℝ) (251045470617/500000000000 : ℝ) (251045470621/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 4 (50209094127/100000000000 : ℝ) (251045470639/500000000000 : ℝ) (251045470617/500000000000 : ℝ) (251045470621/500000000000 : ℝ) (125522735313/250000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 5 (125522735313/250000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 6 (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33815/262144 : ℝ))) 7 (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33815/262144 : ℝ)) hmem 8 (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33815/262144 : ℝ))) hcmem 8 (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33815/262144 : ℝ)) (495993203257/500000000000 : ℝ) (991986406517/1000000000000 : ℝ) (502090941251/1000000000000 : ℝ) (25104547063/50000000000 : ℝ) (795053844541/1000000000000 : ℝ) (397526922279/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1382_exp_lower
  have heNumeric : (2054907202309/1000000000000 : ℝ)/4 ≤ Real.exp (-21314037478981/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907202309/1000000000000 : ℝ)/4 ≤ Real.exp ((16907/131072 : ℝ)-(397526922279/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16907/131072 : ℝ) (33815/262144 : ℝ) (397526922279/500000000000 : ℝ) (2054907202309/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1383; no trusted numerical premise.
theorem cover8_leaf1383_exp_radius : (62374152454442147/62500000000000000 : ℝ) ≤ Real.exp ((-4227/262144 : ℝ)/8) ∧ Real.exp ((-4227/262144 : ℝ)/8) ≤ (997986439271074353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4227/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1383_exp_lower : (230028442035683061/250000000000000000 : ℝ) ≤ Real.exp ((-8525614649317/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525614649317/12800000000000 : ℝ)/8) ≤ (184022753628546449/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525614649317/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1383_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453628629/500000000000 : ℝ) ≤ 4*Real.exp (33815/262144 : ℝ)*Real.exp (-mu (radius 8 (4227/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453628629/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4227/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1383_exp_radius
  have hrNumeric : (984004582093/1000000000000 : ℝ) ≤ Real.exp (-4227/262144 : ℝ) ∧ Real.exp (-4227/262144 : ℝ) ≤ (492002291047/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984004582093/1000000000000 : ℝ) ≤ (radius 8 (4227/32768 : ℝ)) ∧ (radius 8 (4227/32768 : ℝ)) ≤ (492002291047/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4227/32768 : ℝ)) (984004582093/1000000000000 : ℝ) (492002291047/500000000000 : ℝ) (44535787869/250000000000 : ℝ) (178143151483/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4227/32768 : ℝ)) (984004582093/1000000000000 : ℝ) (492002291047/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984004582093/1000000000000 : ℝ) (492002291047/500000000000 : ℝ) (496001145523/500000000000 : ℝ) (992002291047/1000000000000 : ℝ) (495985025503/500000000000 : ℝ) (991970051007/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 1 (496001145523/500000000000 : ℝ) (992002291047/1000000000000 : ℝ) (495985025503/500000000000 : ℝ) (991970051007/1000000000000 : ℝ) (495993085513/500000000000 : ℝ) (991986171027/1000000000000 : ℝ) (198397234179/200000000000 : ℝ) (991986170897/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 2 (495993085513/500000000000 : ℝ) (991986171027/1000000000000 : ℝ) (198397234179/200000000000 : ℝ) (991986170897/1000000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 3 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 4 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 5 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 6 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4227/32768 : ℝ)) 7 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4227/32768 : ℝ))) (44535787869/250000000000 : ℝ) (178143151483/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44535787869/250000000000 : ℝ) (178143151483/1000000000000 : ℝ) (294535787869/500000000000 : ℝ) (294535787871/500000000000 : ℝ) (105517519717/250000000000 : ℝ) (422070078877/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 1 (294535787869/500000000000 : ℝ) (294535787871/500000000000 : ℝ) (105517519717/250000000000 : ℝ) (422070078877/1000000000000 : ℝ) (505570827303/1000000000000 : ℝ) (50557082731/100000000000 : ℝ) (124656900739/250000000000 : ℝ) (99725520593/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 2 (505570827303/1000000000000 : ℝ) (50557082731/100000000000 : ℝ) (124656900739/250000000000 : ℝ) (99725520593/200000000000 : ℝ) (502099215129/1000000000000 : ℝ) (251049607569/500000000000 : ℝ) (502087213283/1000000000000 : ℝ) (125521803323/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 3 (502099215129/1000000000000 : ℝ) (251049607569/500000000000 : ℝ) (502087213283/1000000000000 : ℝ) (125521803323/250000000000 : ℝ) (251046607103/500000000000 : ℝ) (100418642843/200000000000 : ℝ) (50209321417/100000000000 : ℝ) (25104660709/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 4 (251046607103/500000000000 : ℝ) (100418642843/200000000000 : ℝ) (50209321417/100000000000 : ℝ) (25104660709/50000000000 : ℝ) (125523303547/250000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 5 (125523303547/250000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 6 (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4227/32768 : ℝ))) 7 (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4227/32768 : ℝ)) hmem 8 (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4227/32768 : ℝ))) hcmem 8 (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4227/32768 : ℝ)) (12399827137/12500000000 : ℝ) (495993085481/500000000000 : ℝ) (502093214187/1000000000000 : ℝ) (251046607099/500000000000 : ℝ) (159011526499/200000000000 : ℝ) (159011526503/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1383_exp_lower
  have heNumeric : (1027453628629/500000000000 : ℝ)/4 ≤ Real.exp (-8525614649317/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453628629/500000000000 : ℝ)/4 ≤ Real.exp ((33815/262144 : ℝ)-(159011526503/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33815/262144 : ℝ) (4227/32768 : ℝ) (159011526503/200000000000 : ℝ) (1027453628629/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1384; no trusted numerical premise.
theorem cover8_leaf1384_exp_radius : (997986379786448921/1000000000000000000 : ℝ) ≤ Real.exp ((-33817/2097152 : ℝ)/8) ∧ Real.exp ((-33817/2097152 : ℝ)/8) ≤ (498993189893224461/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33817/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1384_exp_lower : (920113771227214179/1000000000000000000 : ℝ) ≤ Real.exp ((-5328508941277/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328508941277/8000000000000 : ℝ)/8) ≤ (46005688561360709/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328508941277/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1384_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907312367/1000000000000 : ℝ) ≤ 4*Real.exp (4227/32768 : ℝ)*Real.exp (-mu (radius 8 (33817/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907312367/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33817/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1384_exp_radius
  have hrNumeric : (984004112883/1000000000000 : ℝ) ≤ Real.exp (-33817/2097152 : ℝ) ∧ Real.exp (-33817/2097152 : ℝ) ≤ (246001028221/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984004112883/1000000000000 : ℝ) ≤ (radius 8 (33817/262144 : ℝ)) ∧ (radius 8 (33817/262144 : ℝ)) ≤ (246001028221/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33817/262144 : ℝ)) (984004112883/1000000000000 : ℝ) (246001028221/250000000000 : ℝ) (178145743219/1000000000000 : ℝ) (89072871613/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33817/262144 : ℝ)) (984004112883/1000000000000 : ℝ) (246001028221/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984004112883/1000000000000 : ℝ) (246001028221/250000000000 : ℝ) (992002056441/1000000000000 : ℝ) (496001028221/500000000000 : ℝ) (991969814501/1000000000000 : ℝ) (991969814503/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 1 (992002056441/1000000000000 : ℝ) (496001028221/500000000000 : ℝ) (991969814501/1000000000000 : ℝ) (991969814503/1000000000000 : ℝ) (991985935471/1000000000000 : ℝ) (991985935473/1000000000000 : ℝ) (49599296767/50000000000 : ℝ) (495992967671/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 2 (991985935471/1000000000000 : ℝ) (991985935473/1000000000000 : ℝ) (49599296767/50000000000 : ℝ) (495992967671/500000000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 3 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 4 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 5 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 6 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33817/262144 : ℝ)) 7 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33817/262144 : ℝ))) (178145743219/1000000000000 : ℝ) (89072871613/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178145743219/1000000000000 : ℝ) (89072871613/500000000000 : ℝ) (589072871609/1000000000000 : ℝ) (589072871613/1000000000000 : ℝ) (105518287283/250000000000 : ℝ) (211036574571/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 1 (589072871609/1000000000000 : ℝ) (589072871613/1000000000000 : ℝ) (105518287283/250000000000 : ℝ) (211036574571/500000000000 : ℝ) (50557301037/100000000000 : ℝ) (252786505189/500000000000 : ℝ) (7791093203/15625000000 : ℝ) (99725993/200000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 2 (50557301037/100000000000 : ℝ) (252786505189/500000000000 : ℝ) (7791093203/15625000000 : ℝ) (99725993/200000000 : ℝ) (502101487681/1000000000000 : ℝ) (502101487689/1000000000000 : ℝ) (502089486507/1000000000000 : ℝ) (125522371629/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 3 (502101487681/1000000000000 : ℝ) (502101487689/1000000000000 : ℝ) (502089486507/1000000000000 : ℝ) (125522371629/250000000000 : ℝ) (251047743547/500000000000 : ℝ) (502095487103/1000000000000 : ℝ) (251047743529/500000000000 : ℝ) (502095487067/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 4 (251047743547/500000000000 : ℝ) (502095487103/1000000000000 : ℝ) (251047743529/500000000000 : ℝ) (502095487067/1000000000000 : ℝ) (125523871769/250000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 5 (125523871769/250000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 6 (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33817/262144 : ℝ))) 7 (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33817/262144 : ℝ)) hmem 8 (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33817/262144 : ℝ))) hcmem 8 (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33817/262144 : ℝ)) (198397187081/200000000000 : ℝ) (61999120963/62500000000 : ℝ) (20083819483/40000000000 : ℝ) (100419097417/200000000000 : ℝ) (6360491363/8000000000 : ℝ) (397530710197/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1384_exp_lower
  have heNumeric : (2054907312367/1000000000000 : ℝ)/4 ≤ Real.exp (-5328508941277/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907312367/1000000000000 : ℝ)/4 ≤ Real.exp ((4227/32768 : ℝ)-(397530710197/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4227/32768 : ℝ) (33817/262144 : ℝ) (397530710197/500000000000 : ℝ) (2054907312367/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1385; no trusted numerical premise.
theorem cover8_leaf1385_exp_radius : (249496580075456759/250000000000000000 : ℝ) ≤ Real.exp ((-16909/1048576 : ℝ)/8) ∧ Real.exp ((-16909/1048576 : ℝ)/8) ≤ (997986320301827037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16909/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1385_exp_lower : (460056887159931067/500000000000000000 : ℝ) ≤ Real.exp ((-42628069809303/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628069809303/64000000000000 : ℝ)/8) ≤ (184022754863972427/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628069809303/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1385_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453683811/500000000000 : ℝ) ≤ 4*Real.exp (33817/262144 : ℝ)*Real.exp (-mu (radius 8 (16909/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453683811/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16909/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1385_exp_radius
  have hrNumeric : (984003643673/1000000000000 : ℝ) ≤ Real.exp (-16909/1048576 : ℝ) ∧ Real.exp (-16909/1048576 : ℝ) ≤ (492001821837/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984003643673/1000000000000 : ℝ) ≤ (radius 8 (16909/131072 : ℝ)) ∧ (radius 8 (16909/131072 : ℝ)) ≤ (492001821837/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16909/131072 : ℝ)) (984003643673/1000000000000 : ℝ) (492001821837/500000000000 : ℝ) (44537083731/250000000000 : ℝ) (17814833493/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16909/131072 : ℝ)) (984003643673/1000000000000 : ℝ) (492001821837/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984003643673/1000000000000 : ℝ) (492001821837/500000000000 : ℝ) (248000455459/250000000000 : ℝ) (992001821837/1000000000000 : ℝ) (991969577997/1000000000000 : ℝ) (991969577999/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 1 (248000455459/250000000000 : ℝ) (992001821837/1000000000000 : ℝ) (991969577997/1000000000000 : ℝ) (991969577999/1000000000000 : ℝ) (247996424979/250000000000 : ℝ) (495992849959/500000000000 : ℝ) (198397139957/200000000000 : ℝ) (991985699787/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 2 (247996424979/250000000000 : ℝ) (495992849959/500000000000 : ℝ) (198397139957/200000000000 : ℝ) (991985699787/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 3 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 4 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 5 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 6 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16909/131072 : ℝ)) 7 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16909/131072 : ℝ))) (44537083731/250000000000 : ℝ) (17814833493/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44537083731/250000000000 : ℝ) (17814833493/100000000000 : ℝ) (294537083731/500000000000 : ℝ) (117814833493/200000000000 : ℝ) (42207621933/100000000000 : ℝ) (211038109669/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 1 (294537083731/500000000000 : ℝ) (117814833493/200000000000 : ℝ) (42207621933/100000000000 : ℝ) (211038109669/500000000000 : ℝ) (126393798349/250000000000 : ℝ) (252787596701/500000000000 : ℝ) (498632326977/1000000000000 : ℝ) (62329040873/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 2 (126393798349/250000000000 : ℝ) (252787596701/500000000000 : ℝ) (498632326977/1000000000000 : ℝ) (62329040873/125000000000 : ℝ) (251051880093/500000000000 : ℝ) (502103760193/1000000000000 : ℝ) (251045879843/500000000000 : ℝ) (502091759693/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 3 (251051880093/500000000000 : ℝ) (502103760193/1000000000000 : ℝ) (251045879843/500000000000 : ℝ) (502091759693/1000000000000 : ℝ) (7845277499/15625000000 : ℝ) (502097759943/1000000000000 : ℝ) (5020977599/10000000000 : ℝ) (125524439977/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 4 (7845277499/15625000000 : ℝ) (502097759943/1000000000000 : ℝ) (5020977599/10000000000 : ℝ) (125524439977/250000000000 : ℝ) (251048879959/500000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 5 (251048879959/500000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 6 (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16909/131072 : ℝ))) 7 (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16909/131072 : ℝ)) hmem 8 (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16909/131072 : ℝ))) hcmem 8 (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16909/131072 : ℝ)) (19839713997/20000000000 : ℝ) (991985699853/1000000000000 : ℝ) (502097759917/1000000000000 : ℝ) (251048879963/500000000000 : ℝ) (99383151023/125000000000 : ℝ) (397532604101/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1385_exp_lower
  have heNumeric : (1027453683811/500000000000 : ℝ)/4 ≤ Real.exp (-42628069809303/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453683811/500000000000 : ℝ)/4 ≤ Real.exp ((33817/262144 : ℝ)-(397532604101/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33817/262144 : ℝ) (16909/131072 : ℝ) (397532604101/500000000000 : ℝ) (1027453683811/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1386; no trusted numerical premise.
theorem cover8_leaf1386_exp_radius : (124748282602151087/125000000000000000 : ℝ) ≤ Real.exp ((-33819/2097152 : ℝ)/8) ∧ Real.exp ((-33819/2097152 : ℝ)/8) ≤ (997986260817208697/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33819/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1386_exp_lower : (920113777422286309/1000000000000000000 : ℝ) ≤ Real.exp ((-852561361659/1280000000000 : ℝ)/8) ∧ Real.exp ((-852561361659/1280000000000 : ℝ)/8) ≤ (92011377742228631/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852561361659/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1386_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726855763/250000000000 : ℝ) ≤ 4*Real.exp (16909/131072 : ℝ)*Real.exp (-mu (radius 8 (33819/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726855763/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33819/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1386_exp_radius
  have hrNumeric : (15375049601/15625000000 : ℝ) ≤ Real.exp (-33819/2097152 : ℝ) ∧ Real.exp (-33819/2097152 : ℝ) ≤ (196800634893/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15375049601/15625000000 : ℝ) ≤ (radius 8 (33819/262144 : ℝ)) ∧ (radius 8 (33819/262144 : ℝ)) ≤ (196800634893/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33819/262144 : ℝ)) (15375049601/15625000000 : ℝ) (196800634893/200000000000 : ℝ) (22268865823/125000000000 : ℝ) (17815092659/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33819/262144 : ℝ)) (15375049601/15625000000 : ℝ) (196800634893/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15375049601/15625000000 : ℝ) (196800634893/200000000000 : ℝ) (31000049601/31250000000 : ℝ) (992001587233/1000000000000 : ℝ) (991969341493/1000000000000 : ℝ) (198393868299/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 1 (31000049601/31250000000 : ℝ) (992001587233/1000000000000 : ℝ) (991969341493/1000000000000 : ℝ) (198393868299/200000000000 : ℝ) (495992732181/500000000000 : ℝ) (247996366091/250000000000 : ℝ) (991985464231/1000000000000 : ℝ) (991985464233/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 2 (495992732181/500000000000 : ℝ) (247996366091/250000000000 : ℝ) (991985464231/1000000000000 : ℝ) (991985464233/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 3 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 4 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 5 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 6 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33819/262144 : ℝ)) 7 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33819/262144 : ℝ))) (22268865823/125000000000 : ℝ) (17815092659/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22268865823/125000000000 : ℝ) (17815092659/100000000000 : ℝ) (147268865823/250000000000 : ℝ) (117815092659/200000000000 : ℝ) (422079289451/1000000000000 : ℝ) (422079289459/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 1 (147268865823/250000000000 : ℝ) (117815092659/200000000000 : ℝ) (422079289451/1000000000000 : ℝ) (422079289459/1000000000000 : ℝ) (505577376371/1000000000000 : ℝ) (505577376377/1000000000000 : ℝ) (62329336113/125000000000 : ℝ) (498634688911/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 2 (505577376371/1000000000000 : ℝ) (505577376377/1000000000000 : ℝ) (62329336113/125000000000 : ℝ) (498634688911/1000000000000 : ℝ) (502106032637/1000000000000 : ℝ) (125526508161/250000000000 : ℝ) (50209403281/100000000000 : ℝ) (502094032817/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 3 (502106032637/1000000000000 : ℝ) (125526508161/250000000000 : ℝ) (50209403281/100000000000 : ℝ) (502094032817/1000000000000 : ℝ) (502100032723/1000000000000 : ℝ) (502100032731/1000000000000 : ℝ) (502100032687/1000000000000 : ℝ) (100420006539/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 4 (502100032723/1000000000000 : ℝ) (502100032731/1000000000000 : ℝ) (502100032687/1000000000000 : ℝ) (100420006539/200000000000 : ℝ) (100420006541/200000000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 5 (100420006541/200000000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 6 (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33819/262144 : ℝ))) 7 (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33819/262144 : ℝ)) hmem 8 (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33819/262144 : ℝ))) hcmem 8 (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33819/262144 : ℝ)) (123998183037/125000000000 : ℝ) (991985464299/1000000000000 : ℝ) (7845313011/15625000000 : ℝ) (502100032713/1000000000000 : ℝ) (795068995907/1000000000000 : ℝ) (31802759837/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1386_exp_lower
  have heNumeric : (513726855763/250000000000 : ℝ)/4 ≤ Real.exp (-852561361659/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726855763/250000000000 : ℝ)/4 ≤ Real.exp ((16909/131072 : ℝ)-(31802759837/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16909/131072 : ℝ) (33819/262144 : ℝ) (31802759837/40000000000 : ℝ) (513726855763/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1387; no trusted numerical premise.
theorem cover8_leaf1387_exp_radius : (498993100666296951/500000000000000000 : ℝ) ≤ Real.exp ((-8455/524288 : ℝ)/8) ∧ Real.exp ((-8455/524288 : ℝ)/8) ≤ (997986201332593903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8455/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1387_exp_lower : (920113780532876503/1000000000000000000 : ℝ) ≤ Real.exp ((-42628066352053/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628066352053/64000000000000 : ℝ)/8) ≤ (115014222566609563/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628066352053/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1387_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907478627/1000000000000 : ℝ) ≤ 4*Real.exp (33819/262144 : ℝ)*Real.exp (-mu (radius 8 (8455/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907478627/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8455/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1387_exp_radius
  have hrNumeric : (196800541051/200000000000 : ℝ) ≤ Real.exp (-8455/524288 : ℝ) ∧ Real.exp (-8455/524288 : ℝ) ≤ (123000338157/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196800541051/200000000000 : ℝ) ≤ (radius 8 (8455/65536 : ℝ)) ∧ (radius 8 (8455/65536 : ℝ)) ≤ (123000338157/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8455/65536 : ℝ)) (196800541051/200000000000 : ℝ) (123000338157/125000000000 : ℝ) (35630703641/200000000000 : ℝ) (178153518211/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8455/65536 : ℝ)) (196800541051/200000000000 : ℝ) (123000338157/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196800541051/200000000000 : ℝ) (123000338157/125000000000 : ℝ) (992001352627/1000000000000 : ℝ) (248000338157/250000000000 : ℝ) (99196910499/100000000000 : ℝ) (991969104991/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 1 (992001352627/1000000000000 : ℝ) (248000338157/250000000000 : ℝ) (99196910499/100000000000 : ℝ) (991969104991/1000000000000 : ℝ) (123998153601/125000000000 : ℝ) (99198522881/100000000000 : ℝ) (991985228677/1000000000000 : ℝ) (991985228679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 2 (123998153601/125000000000 : ℝ) (99198522881/100000000000 : ℝ) (991985228677/1000000000000 : ℝ) (991985228679/1000000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 3 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 4 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 5 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 6 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8455/65536 : ℝ)) 7 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8455/65536 : ℝ))) (35630703641/200000000000 : ℝ) (178153518211/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35630703641/200000000000 : ℝ) (178153518211/1000000000000 : ℝ) (294538379551/500000000000 : ℝ) (294538379553/500000000000 : ℝ) (26380147469/62500000000 : ℝ) (52760294939/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 1 (294538379551/500000000000 : ℝ) (294538379553/500000000000 : ℝ) (26380147469/62500000000 : ℝ) (52760294939/125000000000 : ℝ) (505579559303/1000000000000 : ℝ) (505579559309/1000000000000 : ℝ) (24931852539/50000000000 : ℝ) (498637050787/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 2 (505579559303/1000000000000 : ℝ) (505579559309/1000000000000 : ℝ) (24931852539/50000000000 : ℝ) (498637050787/1000000000000 : ℝ) (502108305041/1000000000000 : ℝ) (62763538131/125000000000 : ℝ) (502096305887/1000000000000 : ℝ) (251048152947/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 3 (502108305041/1000000000000 : ℝ) (62763538131/125000000000 : ℝ) (502096305887/1000000000000 : ℝ) (251048152947/500000000000 : ℝ) (62762788183/125000000000 : ℝ) (502102305471/1000000000000 : ℝ) (125525576357/250000000000 : ℝ) (125525576359/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 4 (62762788183/125000000000 : ℝ) (502102305471/1000000000000 : ℝ) (125525576357/250000000000 : ℝ) (125525576359/250000000000 : ℝ) (251051152723/500000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 5 (251051152723/500000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 6 (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8455/65536 : ℝ))) 7 (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8455/65536 : ℝ)) hmem 8 (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8455/65536 : ℝ))) hcmem 8 (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8455/65536 : ℝ)) (495992614371/500000000000 : ℝ) (198397045749/200000000000 : ℝ) (100420461089/200000000000 : ℝ) (251051152727/500000000000 : ℝ) (795072783559/1000000000000 : ℝ) (795072783577/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1387_exp_lower
  have heNumeric : (2054907478627/1000000000000 : ℝ)/4 ≤ Real.exp (-42628066352053/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907478627/1000000000000 : ℝ)/4 ≤ Real.exp ((33819/262144 : ℝ)-(795072783577/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33819/262144 : ℝ) (8455/65536 : ℝ) (795072783577/1000000000000 : ℝ) (2054907478627/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1388; no trusted numerical premise.
theorem cover8_leaf1388_exp_radius : (498993070923991327/500000000000000000 : ℝ) ≤ Real.exp ((-33821/2097152 : ℝ)/8) ∧ Real.exp ((-33821/2097152 : ℝ)/8) ≤ (199597228369596531/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33821/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1388_exp_lower : (920113783652207789/1000000000000000000 : ℝ) ≤ Real.exp ((-10657016154073/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657016154073/16000000000000 : ℝ)/8) ≤ (92011378365220779/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657016154073/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1388_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907534359/1000000000000 : ℝ) ≤ 4*Real.exp (8455/65536 : ℝ)*Real.exp (-mu (radius 8 (33821/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907534359/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33821/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1388_exp_radius
  have hrNumeric : (492001118023/500000000000 : ℝ) ≤ Real.exp (-33821/2097152 : ℝ) ∧ Real.exp (-33821/2097152 : ℝ) ≤ (984002236047/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492001118023/500000000000 : ℝ) ≤ (radius 8 (33821/262144 : ℝ)) ∧ (radius 8 (33821/262144 : ℝ)) ≤ (984002236047/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33821/262144 : ℝ)) (492001118023/500000000000 : ℝ) (984002236047/1000000000000 : ℝ) (178156109787/1000000000000 : ℝ) (178156109793/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33821/262144 : ℝ)) (492001118023/500000000000 : ℝ) (984002236047/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492001118023/500000000000 : ℝ) (984002236047/1000000000000 : ℝ) (992001118023/1000000000000 : ℝ) (124000139753/125000000000 : ℝ) (495984434243/500000000000 : ℝ) (991968868487/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 1 (992001118023/1000000000000 : ℝ) (124000139753/125000000000 : ℝ) (495984434243/500000000000 : ℝ) (991968868487/1000000000000 : ℝ) (495992496627/500000000000 : ℝ) (123998124157/125000000000 : ℝ) (991984993123/1000000000000 : ℝ) (1587175989/1600000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 2 (495992496627/500000000000 : ℝ) (123998124157/125000000000 : ℝ) (991984993123/1000000000000 : ℝ) (1587175989/1600000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 3 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 4 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 5 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 6 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33821/262144 : ℝ)) 7 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33821/262144 : ℝ))) (178156109787/1000000000000 : ℝ) (178156109793/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178156109787/1000000000000 : ℝ) (178156109793/1000000000000 : ℝ) (589078054893/1000000000000 : ℝ) (589078054897/1000000000000 : ℝ) (422085429489/1000000000000 : ℝ) (422085429497/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 1 (589078054893/1000000000000 : ℝ) (589078054897/1000000000000 : ℝ) (422085429489/1000000000000 : ℝ) (422085429497/1000000000000 : ℝ) (505581742191/1000000000000 : ℝ) (505581742197/1000000000000 : ℝ) (498639412603/1000000000000 : ℝ) (498639412611/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 2 (505581742191/1000000000000 : ℝ) (505581742197/1000000000000 : ℝ) (498639412603/1000000000000 : ℝ) (498639412611/1000000000000 : ℝ) (502110577397/1000000000000 : ℝ) (125527644351/250000000000 : ℝ) (100419715783/200000000000 : ℝ) (502098578923/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 3 (502110577397/1000000000000 : ℝ) (125527644351/250000000000 : ℝ) (100419715783/200000000000 : ℝ) (502098578923/1000000000000 : ℝ) (125526144539/250000000000 : ℝ) (125526144541/250000000000 : ℝ) (12552614453/25000000000 : ℝ) (31381536133/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 4 (125526144539/250000000000 : ℝ) (125526144541/250000000000 : ℝ) (12552614453/25000000000 : ℝ) (31381536133/62500000000 : ℝ) (251052289069/500000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 5 (251052289069/500000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 6 (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33821/262144 : ℝ))) 7 (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33821/262144 : ℝ)) hmem 8 (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33821/262144 : ℝ))) hcmem 8 (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33821/262144 : ℝ)) (247996248297/250000000000 : ℝ) (991984993191/1000000000000 : ℝ) (502104578137/1000000000000 : ℝ) (251052289073/500000000000 : ℝ) (159015314227/200000000000 : ℝ) (795076571153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1388_exp_lower
  have heNumeric : (2054907534359/1000000000000 : ℝ)/4 ≤ Real.exp (-10657016154073/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907534359/1000000000000 : ℝ)/4 ≤ Real.exp ((8455/65536 : ℝ)-(795076571153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8455/65536 : ℝ) (33821/262144 : ℝ) (795076571153/1000000000000 : ℝ) (2054907534359/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1389; no trusted numerical premise.
theorem cover8_leaf1389_exp_radius : (997986082363374951/1000000000000000000 : ℝ) ≤ Real.exp ((-16911/1048576 : ℝ)/8) ∧ Real.exp ((-16911/1048576 : ℝ)/8) ≤ (124748260295421869/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16911/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1389_exp_lower : (230028446694983781/250000000000000000 : ℝ) ≤ Real.exp ((-42628062875859/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628062875859/64000000000000 : ℝ)/8) ≤ (7360910294239481/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628062875859/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1389_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907590241/1000000000000 : ℝ) ≤ 4*Real.exp (33821/262144 : ℝ)*Real.exp (-mu (radius 8 (16911/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907590241/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16911/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1389_exp_radius
  have hrNumeric : (984001766837/1000000000000 : ℝ) ≤ Real.exp (-16911/1048576 : ℝ) ∧ Real.exp (-16911/1048576 : ℝ) ≤ (492000883419/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984001766837/1000000000000 : ℝ) ≤ (radius 8 (16911/131072 : ℝ)) ∧ (radius 8 (16911/131072 : ℝ)) ≤ (492000883419/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16911/131072 : ℝ)) (984001766837/1000000000000 : ℝ) (492000883419/500000000000 : ℝ) (17815870133/100000000000 : ℝ) (22269837667/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16911/131072 : ℝ)) (984001766837/1000000000000 : ℝ) (492000883419/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984001766837/1000000000000 : ℝ) (492000883419/500000000000 : ℝ) (496000441709/500000000000 : ℝ) (992000883419/1000000000000 : ℝ) (495984315991/500000000000 : ℝ) (991968631983/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 1 (496000441709/500000000000 : ℝ) (992000883419/1000000000000 : ℝ) (495984315991/500000000000 : ℝ) (991968631983/1000000000000 : ℝ) (9919847577/10000000000 : ℝ) (991984757701/1000000000000 : ℝ) (15499761837/15625000000 : ℝ) (99198475757/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 2 (9919847577/10000000000 : ℝ) (991984757701/1000000000000 : ℝ) (15499761837/15625000000 : ℝ) (99198475757/100000000000 : ℝ) (495992378817/500000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 3 (495992378817/500000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 4 (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 5 (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 6 (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16911/131072 : ℝ)) 7 (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16911/131072 : ℝ))) (17815870133/100000000000 : ℝ) (22269837667/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17815870133/100000000000 : ℝ) (22269837667/125000000000 : ℝ) (117815870133/200000000000 : ℝ) (147269837667/250000000000 : ℝ) (84417699881/200000000000 : ℝ) (422088499413/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 1 (117815870133/200000000000 : ℝ) (147269837667/250000000000 : ℝ) (84417699881/200000000000 : ℝ) (422088499413/1000000000000 : ℝ) (101116785007/200000000000 : ℝ) (505583925041/1000000000000 : ℝ) (797826839/1600000000 : ℝ) (249320887191/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 2 (101116785007/200000000000 : ℝ) (505583925041/1000000000000 : ℝ) (797826839/1600000000 : ℝ) (249320887191/500000000000 : ℝ) (100422569941/200000000000 : ℝ) (31382053107/62500000000 : ℝ) (62762606487/125000000000 : ℝ) (502100851903/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 3 (100422569941/200000000000 : ℝ) (31382053107/62500000000 : ℝ) (62762606487/125000000000 : ℝ) (502100851903/1000000000000 : ℝ) (1255267127/2500000000 : ℝ) (62763356351/125000000000 : ℝ) (125526712691/250000000000 : ℝ) (125526712693/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 4 (1255267127/2500000000 : ℝ) (62763356351/125000000000 : ℝ) (125526712691/250000000000 : ℝ) (125526712693/250000000000 : ℝ) (251053425391/500000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 5 (251053425391/500000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 6 (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16911/131072 : ℝ))) 7 (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16911/131072 : ℝ)) hmem 8 (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16911/131072 : ℝ))) hcmem 8 (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16911/131072 : ℝ)) (991984757633/1000000000000 : ℝ) (247996189409/250000000000 : ℝ) (502106850781/1000000000000 : ℝ) (50210685079/100000000000 : ℝ) (397540179319/500000000000 : ℝ) (3105782651/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1389_exp_lower
  have heNumeric : (2054907590241/1000000000000 : ℝ)/4 ≤ Real.exp (-42628062875859/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907590241/1000000000000 : ℝ)/4 ≤ Real.exp ((33821/262144 : ℝ)-(3105782651/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33821/262144 : ℝ) (16911/131072 : ℝ) (3105782651/3906250000 : ℝ) (2054907590241/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1390; no trusted numerical premise.
theorem cover8_leaf1390_exp_radius : (498993011439385397/500000000000000000 : ℝ) ≤ Real.exp ((-33823/2097152 : ℝ)/8) ∧ Real.exp ((-33823/2097152 : ℝ)/8) ≤ (199597204575754159/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33823/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1390_exp_lower : (920113789917093637/1000000000000000000 : ℝ) ≤ Real.exp ((-21314030565089/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314030565089/32000000000000 : ℝ)/8) ≤ (460056894958546819/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314030565089/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1390_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907646291/1000000000000 : ℝ) ≤ 4*Real.exp (16911/131072 : ℝ)*Real.exp (-mu (radius 8 (33823/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907646291/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33823/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1390_exp_radius
  have hrNumeric : (984001297629/1000000000000 : ℝ) ≤ Real.exp (-33823/2097152 : ℝ) ∧ Real.exp (-33823/2097152 : ℝ) ≤ (98400129763/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984001297629/1000000000000 : ℝ) ≤ (radius 8 (33823/262144 : ℝ)) ∧ (radius 8 (33823/262144 : ℝ)) ≤ (98400129763/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33823/262144 : ℝ)) (984001297629/1000000000000 : ℝ) (98400129763/100000000000 : ℝ) (44540323207/250000000000 : ℝ) (35632258567/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33823/262144 : ℝ)) (984001297629/1000000000000 : ℝ) (98400129763/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984001297629/1000000000000 : ℝ) (98400129763/100000000000 : ℝ) (496000324407/500000000000 : ℝ) (198400129763/200000000000 : ℝ) (495984197739/500000000000 : ℝ) (24799209887/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 1 (496000324407/500000000000 : ℝ) (198400129763/200000000000 : ℝ) (495984197739/500000000000 : ℝ) (24799209887/25000000000 : ℝ) (495992261073/500000000000 : ℝ) (247996130537/250000000000 : ℝ) (495992261007/500000000000 : ℝ) (991984522017/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 2 (495992261073/500000000000 : ℝ) (247996130537/250000000000 : ℝ) (495992261007/500000000000 : ℝ) (991984522017/1000000000000 : ℝ) (6199903263/6250000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 3 (6199903263/6250000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 4 (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 5 (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 6 (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33823/262144 : ℝ)) 7 (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33823/262144 : ℝ))) (44540323207/250000000000 : ℝ) (35632258567/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44540323207/250000000000 : ℝ) (35632258567/200000000000 : ℝ) (294540323207/500000000000 : ℝ) (294540323209/500000000000 : ℝ) (84418313849/200000000000 : ℝ) (211045784627/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 1 (294540323207/500000000000 : ℝ) (294540323209/500000000000 : ℝ) (84418313849/200000000000 : ℝ) (211045784627/500000000000 : ℝ) (505586107829/1000000000000 : ℝ) (126396526959/250000000000 : ℝ) (498644136089/1000000000000 : ℝ) (498644136097/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 2 (505586107829/1000000000000 : ℝ) (126396526959/250000000000 : ℝ) (498644136089/1000000000000 : ℝ) (498644136097/1000000000000 : ℝ) (502115121959/1000000000000 : ℝ) (502115121967/1000000000000 : ℝ) (251051562411/500000000000 : ℝ) (502103124831/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 3 (502115121959/1000000000000 : ℝ) (502115121967/1000000000000 : ℝ) (251051562411/500000000000 : ℝ) (502103124831/1000000000000 : ℝ) (50210912339/100000000000 : ℝ) (502109123399/1000000000000 : ℝ) (251054561677/500000000000 : ℝ) (125527280841/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 4 (50210912339/100000000000 : ℝ) (502109123399/1000000000000 : ℝ) (251054561677/500000000000 : ℝ) (125527280841/250000000000 : ℝ) (125527280843/250000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 5 (125527280843/250000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 6 (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33823/262144 : ℝ))) 7 (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33823/262144 : ℝ)) hmem 8 (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33823/262144 : ℝ))) hcmem 8 (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33823/262144 : ℝ)) (991984522079/1000000000000 : ℝ) (991984522083/1000000000000 : ℝ) (502109123371/1000000000000 : ℝ) (251054561691/500000000000 : ℝ) (99385518257/125000000000 : ℝ) (795084146077/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1390_exp_lower
  have heNumeric : (2054907646291/1000000000000 : ℝ)/4 ≤ Real.exp (-21314030565089/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907646291/1000000000000 : ℝ)/4 ≤ Real.exp ((16911/131072 : ℝ)-(795084146077/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16911/131072 : ℝ) (33823/262144 : ℝ) (795084146077/1000000000000 : ℝ) (2054907646291/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1391; no trusted numerical premise.
theorem cover8_leaf1391_exp_radius : (498992981697085091/500000000000000000 : ℝ) ≤ Real.exp ((-1057/65536 : ℝ)/8) ∧ Real.exp ((-1057/65536 : ℝ)/8) ≤ (997985963394170183/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1057/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1391_exp_lower : (28753556033186191/31250000000000000 : ℝ) ≤ Real.exp ((-42628059380209/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628059380209/64000000000000 : ℝ)/8) ≤ (920113793061958113/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628059380209/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1391_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907702479/1000000000000 : ℝ) ≤ 4*Real.exp (33823/262144 : ℝ)*Real.exp (-mu (radius 8 (1057/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907702479/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1057/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1391_exp_radius
  have hrNumeric : (49200041421/50000000000 : ℝ) ≤ Real.exp (-1057/65536 : ℝ) ∧ Real.exp (-1057/65536 : ℝ) ≤ (984000828421/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49200041421/50000000000 : ℝ) ≤ (radius 8 (1057/8192 : ℝ)) ∧ (radius 8 (1057/8192 : ℝ)) ≤ (984000828421/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1057/8192 : ℝ)) (49200041421/50000000000 : ℝ) (984000828421/1000000000000 : ℝ) (89081942147/500000000000 : ℝ) (1781638843/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1057/8192 : ℝ)) (49200041421/50000000000 : ℝ) (984000828421/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49200041421/50000000000 : ℝ) (984000828421/1000000000000 : ℝ) (99200041421/100000000000 : ℝ) (992000414211/1000000000000 : ℝ) (495984079487/500000000000 : ℝ) (3874875621/3906250000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 1 (99200041421/100000000000 : ℝ) (992000414211/1000000000000 : ℝ) (495984079487/500000000000 : ℝ) (3874875621/3906250000 : ℝ) (7749877239/7812500000 : ℝ) (495992143297/500000000000 : ℝ) (49599214323/50000000000 : ℝ) (991984286463/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 2 (7749877239/7812500000 : ℝ) (495992143297/500000000000 : ℝ) (49599214323/50000000000 : ℝ) (991984286463/1000000000000 : ℝ) (495992143263/500000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 3 (495992143263/500000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 4 (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 5 (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 6 (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1057/8192 : ℝ)) 7 (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1057/8192 : ℝ))) (89081942147/500000000000 : ℝ) (1781638843/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89081942147/500000000000 : ℝ) (1781638843/10000000000 : ℝ) (589081942147/1000000000000 : ℝ) (11781638843/20000000000 : ℝ) (16883785561/40000000000 : ℝ) (422094639033/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 1 (589081942147/1000000000000 : ℝ) (11781638843/20000000000 : ℝ) (16883785561/40000000000 : ℝ) (422094639033/1000000000000 : ℝ) (252794145293/500000000000 : ℝ) (15799634081/31250000000 : ℝ) (249323248879/500000000000 : ℝ) (99729299553/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 2 (252794145293/500000000000 : ℝ) (15799634081/31250000000 : ℝ) (249323248879/500000000000 : ℝ) (99729299553/200000000000 : ℝ) (125529348543/250000000000 : ℝ) (502117394179/1000000000000 : ℝ) (125526349427/250000000000 : ℝ) (125526349429/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 3 (125529348543/250000000000 : ℝ) (502117394179/1000000000000 : ℝ) (125526349427/250000000000 : ℝ) (125526349429/250000000000 : ℝ) (25105569797/50000000000 : ℝ) (125527848987/250000000000 : ℝ) (7845490561/15625000000 : ℝ) (62763924489/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 4 (25105569797/50000000000 : ℝ) (125527848987/250000000000 : ℝ) (7845490561/15625000000 : ℝ) (62763924489/125000000000 : ℝ) (251055697961/500000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 5 (251055697961/500000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 6 (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1057/8192 : ℝ))) 7 (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1057/8192 : ℝ)) hmem 8 (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1057/8192 : ℝ))) hcmem 8 (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1057/8192 : ℝ)) (39679371461/40000000000 : ℝ) (991984286529/1000000000000 : ℝ) (502111395921/1000000000000 : ℝ) (50211139593/100000000000 : ℝ) (795087933413/1000000000000 : ℝ) (795087933431/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1391_exp_lower
  have heNumeric : (2054907702479/1000000000000 : ℝ)/4 ≤ Real.exp (-42628059380209/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907702479/1000000000000 : ℝ)/4 ≤ Real.exp ((33823/262144 : ℝ)-(795087933431/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33823/262144 : ℝ) (1057/8192 : ℝ) (795087933431/1000000000000 : ℝ) (2054907702479/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1392; no trusted numerical premise.
theorem cover8_leaf1392_exp_radius : (249496475977393279/250000000000000000 : ℝ) ≤ Real.exp ((-33825/2097152 : ℝ)/8) ∧ Real.exp ((-33825/2097152 : ℝ)/8) ≤ (997985903909573117/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33825/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1392_exp_lower : (920113796216368779/1000000000000000000 : ℝ) ≤ Real.exp ((-1332126800779/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332126800779/2000000000000 : ℝ)/8) ≤ (46005689810818439/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332126800779/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1392_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907758837/1000000000000 : ℝ) ≤ 4*Real.exp (1057/8192 : ℝ)*Real.exp (-mu (radius 8 (33825/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907758837/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33825/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1392_exp_radius
  have hrNumeric : (246000089803/250000000000 : ℝ) ≤ Real.exp (-33825/2097152 : ℝ) ∧ Real.exp (-33825/2097152 : ℝ) ≤ (984000359213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246000089803/250000000000 : ℝ) ≤ (radius 8 (33825/262144 : ℝ)) ∧ (radius 8 (33825/262144 : ℝ)) ≤ (984000359213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33825/262144 : ℝ)) (246000089803/250000000000 : ℝ) (984000359213/1000000000000 : ℝ) (89083237857/500000000000 : ℝ) (178166475721/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33825/262144 : ℝ)) (246000089803/250000000000 : ℝ) (984000359213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246000089803/250000000000 : ℝ) (984000359213/1000000000000 : ℝ) (496000089803/500000000000 : ℝ) (992000179607/1000000000000 : ℝ) (991967922471/1000000000000 : ℝ) (123995990309/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 1 (496000089803/500000000000 : ℝ) (992000179607/1000000000000 : ℝ) (991967922471/1000000000000 : ℝ) (123995990309/125000000000 : ℝ) (495992025519/500000000000 : ℝ) (6199900319/6250000000 : ℝ) (991984050907/1000000000000 : ℝ) (991984050909/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 2 (495992025519/500000000000 : ℝ) (6199900319/6250000000 : ℝ) (991984050907/1000000000000 : ℝ) (991984050909/1000000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 3 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 4 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 5 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 6 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33825/262144 : ℝ)) 7 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33825/262144 : ℝ))) (89083237857/500000000000 : ℝ) (178166475721/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89083237857/500000000000 : ℝ) (178166475721/1000000000000 : ℝ) (589083237857/1000000000000 : ℝ) (589083237861/1000000000000 : ℝ) (52762213591/125000000000 : ℝ) (422097708737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 1 (589083237857/1000000000000 : ℝ) (589083237861/1000000000000 : ℝ) (52762213591/125000000000 : ℝ) (422097708737/1000000000000 : ℝ) (126397618323/250000000000 : ℝ) (505590473299/1000000000000 : ℝ) (62331107421/125000000000 : ℝ) (31165553711/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 2 (126397618323/250000000000 : ℝ) (505590473299/1000000000000 : ℝ) (62331107421/125000000000 : ℝ) (31165553711/62500000000 : ℝ) (50211966633/100000000000 : ℝ) (251059833169/500000000000 : ℝ) (502107670539/1000000000000 : ℝ) (502107670547/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 3 (50211966633/100000000000 : ℝ) (251059833169/500000000000 : ℝ) (502107670539/1000000000000 : ℝ) (502107670547/1000000000000 : ℝ) (251056834217/500000000000 : ℝ) (502113668443/1000000000000 : ℝ) (251056834199/500000000000 : ℝ) (502113668407/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 4 (251056834217/500000000000 : ℝ) (502113668443/1000000000000 : ℝ) (251056834199/500000000000 : ℝ) (502113668407/1000000000000 : ℝ) (7845526069/15625000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 5 (7845526069/15625000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 6 (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33825/262144 : ℝ))) 7 (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33825/262144 : ℝ)) hmem 8 (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33825/262144 : ℝ))) hcmem 8 (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33825/262144 : ℝ)) (247996012743/250000000000 : ℝ) (39679362039/40000000000 : ℝ) (100422733683/200000000000 : ℝ) (20084546737/40000000000 : ℝ) (397545860341/500000000000 : ℝ) (397545860351/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1392_exp_lower
  have heNumeric : (2054907758837/1000000000000 : ℝ)/4 ≤ Real.exp (-1332126800779/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907758837/1000000000000 : ℝ)/4 ≤ Real.exp ((1057/8192 : ℝ)-(397545860351/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1057/8192 : ℝ) (33825/262144 : ℝ) (397545860351/500000000000 : ℝ) (2054907758837/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1393; no trusted numerical premise.
theorem cover8_leaf1393_exp_radius : (199597168884995919/200000000000000000 : ℝ) ≤ Real.exp ((-16913/1048576 : ℝ)/8) ∧ Real.exp ((-16913/1048576 : ℝ)/8) ≤ (249496461106244899/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16913/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1393_exp_lower : (184022759875996119/200000000000000000 : ℝ) ≤ Real.exp ((-42628055864527/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628055864527/64000000000000 : ℝ)/8) ≤ (230028449844995149/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628055864527/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1393_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (6421586923/3125000000 : ℝ) ≤ 4*Real.exp (33825/262144 : ℝ)*Real.exp (-mu (radius 8 (16913/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (6421586923/3125000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16913/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1393_exp_radius
  have hrNumeric : (196799978001/200000000000 : ℝ) ≤ Real.exp (-16913/1048576 : ℝ) ∧ Real.exp (-16913/1048576 : ℝ) ≤ (491999945003/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196799978001/200000000000 : ℝ) ≤ (radius 8 (16913/131072 : ℝ)) ∧ (radius 8 (16913/131072 : ℝ)) ≤ (491999945003/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16913/131072 : ℝ)) (196799978001/200000000000 : ℝ) (491999945003/500000000000 : ℝ) (178169067091/1000000000000 : ℝ) (178169067097/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16913/131072 : ℝ)) (196799978001/200000000000 : ℝ) (491999945003/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196799978001/200000000000 : ℝ) (491999945003/500000000000 : ℝ) (495999972501/500000000000 : ℝ) (991999945003/1000000000000 : ℝ) (61997980373/62500000000 : ℝ) (991967685969/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 1 (495999972501/500000000000 : ℝ) (991999945003/1000000000000 : ℝ) (61997980373/62500000000 : ℝ) (991967685969/1000000000000 : ℝ) (198396763097/200000000000 : ℝ) (495991907743/500000000000 : ℝ) (991983815353/1000000000000 : ℝ) (198396763071/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 2 (198396763097/200000000000 : ℝ) (495991907743/500000000000 : ℝ) (991983815353/1000000000000 : ℝ) (198396763071/200000000000 : ℝ) (991983815419/1000000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 3 (991983815419/1000000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 4 (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 5 (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 6 (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16913/131072 : ℝ)) 7 (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16913/131072 : ℝ))) (178169067091/1000000000000 : ℝ) (178169067097/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178169067091/1000000000000 : ℝ) (178169067097/1000000000000 : ℝ) (117816906709/200000000000 : ℝ) (589084533549/1000000000000 : ℝ) (211050389179/500000000000 : ℝ) (211050389183/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 1 (117816906709/200000000000 : ℝ) (589084533549/1000000000000 : ℝ) (211050389179/500000000000 : ℝ) (211050389183/500000000000 : ℝ) (505592655951/1000000000000 : ℝ) (252796327979/500000000000 : ℝ) (498651220923/1000000000000 : ℝ) (49865122093/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 2 (505592655951/1000000000000 : ℝ) (252796327979/500000000000 : ℝ) (498651220923/1000000000000 : ℝ) (49865122093/100000000000 : ℝ) (502121938437/1000000000000 : ℝ) (125530484611/250000000000 : ℝ) (251054971659/500000000000 : ℝ) (251054971663/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 3 (502121938437/1000000000000 : ℝ) (125530484611/250000000000 : ℝ) (251054971659/500000000000 : ℝ) (251054971663/500000000000 : ℝ) (502115940877/1000000000000 : ℝ) (100423188177/200000000000 : ℝ) (502115940841/1000000000000 : ℝ) (10042318817/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 4 (502115940877/1000000000000 : ℝ) (100423188177/200000000000 : ℝ) (502115940841/1000000000000 : ℝ) (10042318817/20000000000 : ℝ) (502115940859/1000000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 5 (502115940859/1000000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 6 (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16913/131072 : ℝ))) 7 (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16913/131072 : ℝ)) hmem 8 (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16913/131072 : ℝ))) hcmem 8 (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16913/131072 : ℝ)) (495991907709/500000000000 : ℝ) (991983815421/1000000000000 : ℝ) (251057970429/500000000000 : ℝ) (125528985217/250000000000 : ℝ) (795095507873/1000000000000 : ℝ) (795095507893/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1393_exp_lower
  have heNumeric : (6421586923/3125000000 : ℝ)/4 ≤ Real.exp (-42628055864527/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (6421586923/3125000000 : ℝ)/4 ≤ Real.exp ((33825/262144 : ℝ)-(795095507893/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33825/262144 : ℝ) (16913/131072 : ℝ) (795095507893/1000000000000 : ℝ) (6421586923/3125000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1394; no trusted numerical premise.
theorem cover8_leaf1394_exp_radius : (997985725455803191/1000000000000000000 : ℝ) ≤ Real.exp ((-8457/524288 : ℝ)/8) ∧ Real.exp ((-8457/524288 : ℝ)/8) ≤ (124748215681975399/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8457/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1394_exp_lower : (920113366987699589/1000000000000000000 : ℝ) ≤ Real.exp ((-21314148235263/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314148235263/32000000000000 : ℝ)/8) ≤ (92011336698769959/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314148235263/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1394_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900090013/1000000000000 : ℝ) ≤ 4*Real.exp (16913/131072 : ℝ)*Real.exp (-mu (radius 8 (8457/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900090013/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8457/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1394_exp_radius
  have hrNumeric : (98399895159/100000000000 : ℝ) ≤ Real.exp (-8457/524288 : ℝ) ∧ Real.exp (-8457/524288 : ℝ) ≤ (983998951591/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98399895159/100000000000 : ℝ) ≤ (radius 8 (8457/65536 : ℝ)) ∧ (radius 8 (8457/65536 : ℝ)) ≤ (983998951591/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8457/65536 : ℝ)) (98399895159/100000000000 : ℝ) (983998951591/1000000000000 : ℝ) (44543562433/250000000000 : ℝ) (178174249739/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8457/65536 : ℝ)) (98399895159/100000000000 : ℝ) (983998951591/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98399895159/100000000000 : ℝ) (983998951591/1000000000000 : ℝ) (198399895159/200000000000 : ℝ) (247999868949/250000000000 : ℝ) (991967212961/1000000000000 : ℝ) (495983606481/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 1 (198399895159/200000000000 : ℝ) (247999868949/250000000000 : ℝ) (991967212961/1000000000000 : ℝ) (495983606481/500000000000 : ℝ) (495991672189/500000000000 : ℝ) (991983344379/1000000000000 : ℝ) (495991672123/500000000000 : ℝ) (123997918031/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 2 (495991672189/500000000000 : ℝ) (991983344379/1000000000000 : ℝ) (495991672123/500000000000 : ℝ) (123997918031/125000000000 : ℝ) (123997918039/125000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 3 (123997918039/125000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 4 (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 5 (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 6 (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8457/65536 : ℝ)) 7 (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8457/65536 : ℝ))) (44543562433/250000000000 : ℝ) (178174249739/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44543562433/250000000000 : ℝ) (178174249739/1000000000000 : ℝ) (294543562433/500000000000 : ℝ) (58908712487/100000000000 : ℝ) (422106917417/1000000000000 : ℝ) (422106917427/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 1 (294543562433/500000000000 : ℝ) (58908712487/100000000000 : ℝ) (422106917417/1000000000000 : ℝ) (422106917427/1000000000000 : ℝ) (505597021141/1000000000000 : ℝ) (505597021149/1000000000000 : ℝ) (12466398597/25000000000 : ℝ) (31165996493/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 2 (505597021141/1000000000000 : ℝ) (505597021149/1000000000000 : ℝ) (12466398597/25000000000 : ℝ) (31165996493/62500000000 : ℝ) (50212648251/100000000000 : ℝ) (502126482519/1000000000000 : ℝ) (502114488737/1000000000000 : ℝ) (251057244373/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 3 (50212648251/100000000000 : ℝ) (502126482519/1000000000000 : ℝ) (502114488737/1000000000000 : ℝ) (251057244373/500000000000 : ℝ) (502120485623/1000000000000 : ℝ) (502120485633/1000000000000 : ℝ) (502120485587/1000000000000 : ℝ) (502120485597/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 4 (502120485623/1000000000000 : ℝ) (502120485633/1000000000000 : ℝ) (502120485587/1000000000000 : ℝ) (502120485597/1000000000000 : ℝ) (100424097121/200000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 5 (100424097121/200000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 6 (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8457/65536 : ℝ))) 7 (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8457/65536 : ℝ)) hmem 8 (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8457/65536 : ℝ))) hcmem 8 (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8457/65536 : ℝ)) (991983344311/1000000000000 : ℝ) (495991672157/500000000000 : ℝ) (125530121401/250000000000 : ℝ) (100424097123/200000000000 : ℝ) (397551541019/500000000000 : ℝ) (795103082059/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1394_exp_lower
  have heNumeric : (2054900090013/1000000000000 : ℝ)/4 ≤ Real.exp (-21314148235263/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900090013/1000000000000 : ℝ)/4 ≤ Real.exp ((16913/131072 : ℝ)-(795103082059/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16913/131072 : ℝ) (8457/65536 : ℝ) (795103082059/1000000000000 : ℝ) (2054900090013/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1395; no trusted numerical premise.
theorem cover8_leaf1395_exp_radius : (997985606486640969/1000000000000000000 : ℝ) ≤ Real.exp ((-16915/1048576 : ℝ)/8) ∧ Real.exp ((-16915/1048576 : ℝ)/8) ≤ (99798560648664097/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16915/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1395_exp_lower : (230028343343509391/250000000000000000 : ℝ) ≤ Real.exp ((-10657073229207/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657073229207/16000000000000 : ℝ)/8) ≤ (184022674674807513/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657073229207/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1395_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450102057/500000000000 : ℝ) ≤ 4*Real.exp (8457/65536 : ℝ)*Real.exp (-mu (radius 8 (16915/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450102057/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16915/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1395_exp_radius
  have hrNumeric : (39359920527/40000000000 : ℝ) ≤ Real.exp (-16915/1048576 : ℝ) ∧ Real.exp (-16915/1048576 : ℝ) ≤ (122999751647/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39359920527/40000000000 : ℝ) ≤ (radius 8 (16915/131072 : ℝ)) ∧ (radius 8 (16915/131072 : ℝ)) ≤ (122999751647/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16915/131072 : ℝ)) (39359920527/40000000000 : ℝ) (122999751647/125000000000 : ℝ) (89089716109/500000000000 : ℝ) (5568107257/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16915/131072 : ℝ)) (39359920527/40000000000 : ℝ) (122999751647/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39359920527/40000000000 : ℝ) (122999751647/125000000000 : ℝ) (991999006587/1000000000000 : ℝ) (247999751647/250000000000 : ℝ) (495983369977/500000000000 : ℝ) (198393347991/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 1 (991999006587/1000000000000 : ℝ) (247999751647/250000000000 : ℝ) (495983369977/500000000000 : ℝ) (198393347991/200000000000 : ℝ) (99198287327/100000000000 : ℝ) (123997859159/125000000000 : ℝ) (991982873139/1000000000000 : ℝ) (991982873141/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 2 (99198287327/100000000000 : ℝ) (123997859159/125000000000 : ℝ) (991982873139/1000000000000 : ℝ) (991982873141/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 3 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 4 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 5 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 6 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16915/131072 : ℝ)) 7 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16915/131072 : ℝ))) (89089716109/500000000000 : ℝ) (5568107257/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89089716109/500000000000 : ℝ) (5568107257/31250000000 : ℝ) (589089716109/1000000000000 : ℝ) (36818107257/62500000000 : ℝ) (105528264051/250000000000 : ℝ) (105528264053/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 1 (589089716109/1000000000000 : ℝ) (36818107257/62500000000 : ℝ) (105528264051/250000000000 : ℝ) (105528264053/250000000000 : ℝ) (126400346539/250000000000 : ℝ) (252800693081/500000000000 : ℝ) (498660666631/1000000000000 : ℝ) (249330333319/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 2 (126400346539/250000000000 : ℝ) (252800693081/500000000000 : ℝ) (498660666631/1000000000000 : ℝ) (249330333319/500000000000 : ℝ) (502131026393/1000000000000 : ℝ) (627663783/1250000000 : ℝ) (100423806793/200000000000 : ℝ) (125529758493/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 3 (502131026393/1000000000000 : ℝ) (627663783/1250000000 : ℝ) (100423806793/200000000000 : ℝ) (125529758493/250000000000 : ℝ) (502125030179/1000000000000 : ℝ) (251062515093/500000000000 : ℝ) (502125030143/1000000000000 : ℝ) (502125030151/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 4 (502125030179/1000000000000 : ℝ) (251062515093/500000000000 : ℝ) (502125030143/1000000000000 : ℝ) (502125030151/1000000000000 : ℝ) (502125030161/1000000000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 5 (502125030161/1000000000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 6 (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16915/131072 : ℝ))) 7 (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16915/131072 : ℝ)) hmem 8 (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16915/131072 : ℝ))) hcmem 8 (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16915/131072 : ℝ)) (247995718301/250000000000 : ℝ) (991982873207/1000000000000 : ℝ) (6276562877/12500000000 : ℝ) (502125030169/1000000000000 : ℝ) (79511065591/100000000000 : ℝ) (795110655927/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1395_exp_lower
  have heNumeric : (1027450102057/500000000000 : ℝ)/4 ≤ Real.exp (-10657073229207/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450102057/500000000000 : ℝ)/4 ≤ Real.exp ((8457/65536 : ℝ)-(795110655927/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8457/65536 : ℝ) (16915/131072 : ℝ) (795110655927/1000000000000 : ℝ) (1027450102057/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1396; no trusted numerical premise.
theorem cover8_leaf1396_exp_radius : (997985487517492929/1000000000000000000 : ℝ) ≤ Real.exp ((-4229/262144 : ℝ)/8) ∧ Real.exp ((-4229/262144 : ℝ)/8) ≤ (99798548751749293/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4229/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1396_exp_lower : (920113379795914963/1000000000000000000 : ℝ) ≤ Real.exp ((-21314144671677/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314144671677/32000000000000 : ℝ)/8) ≤ (230028344948978741/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314144671677/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1396_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900318851/1000000000000 : ℝ) ≤ 4*Real.exp (16915/131072 : ℝ)*Real.exp (-mu (radius 8 (4229/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900318851/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4229/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1396_exp_radius
  have hrNumeric : (491998537381/500000000000 : ℝ) ≤ Real.exp (-4229/262144 : ℝ) ∧ Real.exp (-4229/262144 : ℝ) ≤ (983997074763/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491998537381/500000000000 : ℝ) ≤ (radius 8 (4229/32768 : ℝ)) ∧ (radius 8 (4229/32768 : ℝ)) ≤ (983997074763/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4229/32768 : ℝ)) (491998537381/500000000000 : ℝ) (983997074763/1000000000000 : ℝ) (178184614537/1000000000000 : ℝ) (178184614543/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4229/32768 : ℝ)) (491998537381/500000000000 : ℝ) (983997074763/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491998537381/500000000000 : ℝ) (983997074763/1000000000000 : ℝ) (991998537381/1000000000000 : ℝ) (495999268691/500000000000 : ℝ) (991966266947/1000000000000 : ℝ) (991966266949/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 1 (991998537381/1000000000000 : ℝ) (495999268691/500000000000 : ℝ) (991966266947/1000000000000 : ℝ) (991966266949/1000000000000 : ℝ) (247995600541/250000000000 : ℝ) (495991201083/500000000000 : ℝ) (61998900127/62500000000 : ℝ) (198396480407/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 2 (247995600541/250000000000 : ℝ) (495991201083/500000000000 : ℝ) (61998900127/62500000000 : ℝ) (198396480407/200000000000 : ℝ) (495991201049/500000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 3 (495991201049/500000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 4 (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 5 (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 6 (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4229/32768 : ℝ)) 7 (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4229/32768 : ℝ))) (178184614537/1000000000000 : ℝ) (178184614543/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178184614537/1000000000000 : ℝ) (178184614543/1000000000000 : ℝ) (147273076817/250000000000 : ℝ) (73636538409/125000000000 : ℝ) (422119194703/1000000000000 : ℝ) (422119194711/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 1 (147273076817/250000000000 : ℝ) (73636538409/125000000000 : ℝ) (422119194703/1000000000000 : ℝ) (422119194711/1000000000000 : ℝ) (101121150197/200000000000 : ℝ) (31600359437/62500000000 : ℝ) (498665389163/1000000000000 : ℝ) (498665389171/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 2 (101121150197/200000000000 : ℝ) (31600359437/62500000000 : ℝ) (498665389163/1000000000000 : ℝ) (498665389171/1000000000000 : ℝ) (251067785037/500000000000 : ℝ) (251067785041/500000000000 : ℝ) (50212357899/100000000000 : ℝ) (251061789499/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 3 (251067785037/500000000000 : ℝ) (251067785041/500000000000 : ℝ) (50212357899/100000000000 : ℝ) (251061789499/500000000000 : ℝ) (125532393633/250000000000 : ℝ) (25106478727/50000000000 : ℝ) (15691549203/31250000000 : ℝ) (100425914901/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 4 (125532393633/250000000000 : ℝ) (25106478727/50000000000 : ℝ) (15691549203/31250000000 : ℝ) (100425914901/200000000000 : ℝ) (251064787257/500000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 5 (251064787257/500000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 6 (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4229/32768 : ℝ))) 7 (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4229/32768 : ℝ)) hmem 8 (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4229/32768 : ℝ))) hcmem 8 (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4229/32768 : ℝ)) (991982402097/1000000000000 : ℝ) (991982402101/1000000000000 : ℝ) (502129574513/1000000000000 : ℝ) (502129574523/1000000000000 : ℝ) (397559114733/500000000000 : ℝ) (397559114743/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1396_exp_lower
  have heNumeric : (2054900318851/1000000000000 : ℝ)/4 ≤ Real.exp (-21314144671677/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900318851/1000000000000 : ℝ)/4 ≤ Real.exp ((16915/131072 : ℝ)-(397559114743/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16915/131072 : ℝ) (4229/32768 : ℝ) (397559114743/500000000000 : ℝ) (2054900318851/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1397; no trusted numerical premise.
theorem cover8_leaf1397_exp_radius : (997985368548359071/1000000000000000000 : ℝ) ≤ Real.exp ((-16917/1048576 : ℝ)/8) ∧ Real.exp ((-16917/1048576 : ℝ)/8) ≤ (31187042767136221/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16917/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1397_exp_lower : (230028346563304193/250000000000000000 : ℝ) ≤ Real.exp ((-5328535718771/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328535718771/8000000000000 : ℝ)/8) ≤ (920113386253216773/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328535718771/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1397_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745021711/50000000000 : ℝ) ≤ 4*Real.exp (4229/32768 : ℝ)*Real.exp (-mu (radius 8 (16917/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (102745021711/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16917/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1397_exp_radius
  have hrNumeric : (19679922727/20000000000 : ℝ) ≤ Real.exp (-16917/1048576 : ℝ) ∧ Real.exp (-16917/1048576 : ℝ) ≤ (983996136351/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19679922727/20000000000 : ℝ) ≤ (radius 8 (16917/131072 : ℝ)) ∧ (radius 8 (16917/131072 : ℝ)) ≤ (983996136351/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16917/131072 : ℝ)) (19679922727/20000000000 : ℝ) (983996136351/1000000000000 : ℝ) (35637959339/200000000000 : ℝ) (178189796701/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16917/131072 : ℝ)) (19679922727/20000000000 : ℝ) (983996136351/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19679922727/20000000000 : ℝ) (983996136351/1000000000000 : ℝ) (39679922727/40000000000 : ℝ) (61999879261/62500000000 : ℝ) (991965793941/1000000000000 : ℝ) (991965793943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 1 (39679922727/40000000000 : ℝ) (61999879261/62500000000 : ℝ) (991965793941/1000000000000 : ℝ) (991965793943/1000000000000 : ℝ) (495990965529/500000000000 : ℝ) (49599096553/50000000000 : ℝ) (495990965463/500000000000 : ℝ) (991981930929/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 2 (495990965529/500000000000 : ℝ) (49599096553/50000000000 : ℝ) (495990965463/500000000000 : ℝ) (991981930929/1000000000000 : ℝ) (61998870687/62500000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 3 (61998870687/62500000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 4 (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 5 (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 6 (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16917/131072 : ℝ)) 7 (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16917/131072 : ℝ))) (35637959339/200000000000 : ℝ) (178189796701/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35637959339/200000000000 : ℝ) (178189796701/1000000000000 : ℝ) (589094898347/1000000000000 : ℝ) (589094898351/1000000000000 : ℝ) (211062666461/500000000000 : ℝ) (42212533293/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 1 (589094898347/1000000000000 : ℝ) (589094898351/1000000000000 : ℝ) (211062666461/500000000000 : ℝ) (42212533293/100000000000 : ℝ) (252805057817/500000000000 : ℝ) (505610115641/1000000000000 : ℝ) (498670111483/1000000000000 : ℝ) (498670111491/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 2 (252805057817/500000000000 : ℝ) (505610115641/1000000000000 : ℝ) (498670111483/1000000000000 : ℝ) (498670111491/1000000000000 : ℝ) (251070056779/500000000000 : ℝ) (251070056783/500000000000 : ℝ) (502128123819/1000000000000 : ℝ) (502128123827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 3 (251070056779/500000000000 : ℝ) (251070056783/500000000000 : ℝ) (502128123819/1000000000000 : ℝ) (502128123827/1000000000000 : ℝ) (15691691209/31250000000 : ℝ) (502134118697/1000000000000 : ℝ) (125533529663/250000000000 : ℝ) (502134118661/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 4 (15691691209/31250000000 : ℝ) (502134118697/1000000000000 : ℝ) (125533529663/250000000000 : ℝ) (502134118661/1000000000000 : ℝ) (50213411867/100000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 5 (50213411867/100000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 6 (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16917/131072 : ℝ))) 7 (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16917/131072 : ℝ)) hmem 8 (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16917/131072 : ℝ))) hcmem 8 (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16917/131072 : ℝ)) (991981930991/1000000000000 : ℝ) (198396386199/200000000000 : ℝ) (502134118669/1000000000000 : ℝ) (502134118679/1000000000000 : ℝ) (795125802717/1000000000000 : ℝ) (795125802737/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1397_exp_lower
  have heNumeric : (102745021711/50000000000 : ℝ)/4 ≤ Real.exp (-5328535718771/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745021711/50000000000 : ℝ)/4 ≤ Real.exp ((4229/32768 : ℝ)-(795125802737/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4229/32768 : ℝ) (16917/131072 : ℝ) (795125802737/1000000000000 : ℝ) (102745021711/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1398; no trusted numerical premise.
theorem cover8_leaf1398_exp_radius : (199597049915847879/200000000000000000 : ℝ) ≤ Real.exp ((-8459/524288 : ℝ)/8) ∧ Real.exp ((-8459/524288 : ℝ)/8) ≤ (249496312394809849/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8459/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1398_exp_lower : (920113392745367921/1000000000000000000 : ℝ) ≤ Real.exp ((-4262828213759/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262828213759/6400000000000 : ℝ)/8) ≤ (460056696372683961/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262828213759/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1398_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725137553/250000000000 : ℝ) ≤ 4*Real.exp (16917/131072 : ℝ)*Real.exp (-mu (radius 8 (8459/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725137553/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8459/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1398_exp_radius
  have hrNumeric : (983995197939/1000000000000 : ℝ) ≤ Real.exp (-8459/524288 : ℝ) ∧ Real.exp (-8459/524288 : ℝ) ≤ (49199759897/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983995197939/1000000000000 : ℝ) ≤ (radius 8 (8459/65536 : ℝ)) ∧ (radius 8 (8459/65536 : ℝ)) ≤ (49199759897/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8459/65536 : ℝ)) (983995197939/1000000000000 : ℝ) (49199759897/50000000000 : ℝ) (178194978691/1000000000000 : ℝ) (89097489349/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8459/65536 : ℝ)) (983995197939/1000000000000 : ℝ) (49199759897/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983995197939/1000000000000 : ℝ) (49199759897/50000000000 : ℝ) (991997598969/1000000000000 : ℝ) (99199759897/100000000000 : ℝ) (198393064187/200000000000 : ℝ) (991965320937/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 1 (991997598969/1000000000000 : ℝ) (99199759897/100000000000 : ℝ) (198393064187/200000000000 : ℝ) (991965320937/1000000000000 : ℝ) (61998841247/62500000000 : ℝ) (495990729977/500000000000 : ℝ) (49599072991/50000000000 : ℝ) (991981459823/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 2 (61998841247/62500000000 : ℝ) (495990729977/500000000000 : ℝ) (49599072991/50000000000 : ℝ) (991981459823/1000000000000 : ℝ) (495990729943/500000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 3 (495990729943/500000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 4 (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 5 (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 6 (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8459/65536 : ℝ)) 7 (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8459/65536 : ℝ))) (178194978691/1000000000000 : ℝ) (89097489349/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178194978691/1000000000000 : ℝ) (89097489349/500000000000 : ℝ) (117819497869/200000000000 : ℝ) (589097489349/1000000000000 : ℝ) (21106573543/50000000000 : ℝ) (422131470869/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 1 (117819497869/200000000000 : ℝ) (589097489349/1000000000000 : ℝ) (21106573543/50000000000 : ℝ) (422131470869/1000000000000 : ℝ) (252807240051/500000000000 : ℝ) (505614480109/1000000000000 : ℝ) (498674833591/1000000000000 : ℝ) (498674833599/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 2 (252807240051/500000000000 : ℝ) (505614480109/1000000000000 : ℝ) (498674833591/1000000000000 : ℝ) (498674833599/1000000000000 : ℝ) (251072328423/500000000000 : ℝ) (251072328427/500000000000 : ℝ) (502132668451/1000000000000 : ℝ) (502132668459/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 3 (251072328423/500000000000 : ℝ) (251072328427/500000000000 : ℝ) (502132668451/1000000000000 : ℝ) (502132668459/1000000000000 : ℝ) (62767332831/125000000000 : ℝ) (502138662657/1000000000000 : ℝ) (125534665653/250000000000 : ℝ) (502138662621/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 4 (62767332831/125000000000 : ℝ) (502138662657/1000000000000 : ℝ) (125534665653/250000000000 : ℝ) (502138662621/1000000000000 : ℝ) (50213866263/100000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 5 (50213866263/100000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 6 (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8459/65536 : ℝ))) 7 (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8459/65536 : ℝ)) hmem 8 (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8459/65536 : ℝ))) hcmem 8 (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8459/65536 : ℝ)) (198396291977/200000000000 : ℝ) (991981459889/1000000000000 : ℝ) (502138662629/1000000000000 : ℝ) (502138662639/1000000000000 : ℝ) (159026675133/200000000000 : ℝ) (159026675137/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1398_exp_lower
  have heNumeric : (513725137553/250000000000 : ℝ)/4 ≤ Real.exp (-4262828213759/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725137553/250000000000 : ℝ)/4 ≤ Real.exp ((16917/131072 : ℝ)-(159026675137/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16917/131072 : ℝ) (8459/65536 : ℝ) (159026675137/200000000000 : ℝ) (513725137553/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1399; no trusted numerical premise.
theorem cover8_leaf1399_exp_radius : (498992565305066951/500000000000000000 : ℝ) ≤ Real.exp ((-16919/1048576 : ℝ)/8) ∧ Real.exp ((-16919/1048576 : ℝ)/8) ≤ (997985130610133903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16919/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1399_exp_lower : (230028349817833321/250000000000000000 : ℝ) ≤ Real.exp ((-10657069626549/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657069626549/16000000000000 : ℝ)/8) ≤ (184022679854266657/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657069626549/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1399_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862583351/125000000000 : ℝ) ≤ 4*Real.exp (8459/65536 : ℝ)*Real.exp (-mu (radius 8 (16919/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862583351/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16919/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1399_exp_radius
  have hrNumeric : (122999282441/125000000000 : ℝ) ≤ Real.exp (-16919/1048576 : ℝ) ∧ Real.exp (-16919/1048576 : ℝ) ≤ (983994259529/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122999282441/125000000000 : ℝ) ≤ (radius 8 (16919/131072 : ℝ)) ∧ (radius 8 (16919/131072 : ℝ)) ≤ (983994259529/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16919/131072 : ℝ)) (122999282441/125000000000 : ℝ) (983994259529/1000000000000 : ℝ) (44550040133/250000000000 : ℝ) (178200160539/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16919/131072 : ℝ)) (122999282441/125000000000 : ℝ) (983994259529/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122999282441/125000000000 : ℝ) (983994259529/1000000000000 : ℝ) (247999282441/250000000000 : ℝ) (198399425953/200000000000 : ℝ) (991964847929/1000000000000 : ℝ) (991964847931/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 1 (247999282441/250000000000 : ℝ) (198399425953/200000000000 : ℝ) (991964847929/1000000000000 : ℝ) (991964847931/1000000000000 : ℝ) (495990494423/500000000000 : ℝ) (61998811803/62500000000 : ℝ) (198396197743/200000000000 : ℝ) (991980988717/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 2 (495990494423/500000000000 : ℝ) (61998811803/62500000000 : ℝ) (198396197743/200000000000 : ℝ) (991980988717/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 3 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 4 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 5 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 6 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16919/131072 : ℝ)) 7 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16919/131072 : ℝ))) (44550040133/250000000000 : ℝ) (178200160539/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44550040133/250000000000 : ℝ) (178200160539/1000000000000 : ℝ) (294550040133/500000000000 : ℝ) (58910008027/100000000000 : ℝ) (16885504341/40000000000 : ℝ) (84427521707/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 1 (294550040133/500000000000 : ℝ) (58910008027/100000000000 : ℝ) (16885504341/40000000000 : ℝ) (84427521707/200000000000 : ℝ) (101123768879/200000000000 : ℝ) (505618844403/1000000000000 : ℝ) (498679555491/1000000000000 : ℝ) (997359111/2000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 2 (101123768879/200000000000 : ℝ) (505618844403/1000000000000 : ℝ) (498679555491/1000000000000 : ℝ) (997359111/2000000000 : ℝ) (502149199943/1000000000000 : ℝ) (31384324997/62500000000 : ℝ) (502137212891/1000000000000 : ℝ) (502137212901/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 3 (502149199943/1000000000000 : ℝ) (31384324997/62500000000 : ℝ) (502137212891/1000000000000 : ℝ) (502137212901/1000000000000 : ℝ) (502143206417/1000000000000 : ℝ) (502143206427/1000000000000 : ℝ) (502143206381/1000000000000 : ℝ) (502143206391/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 4 (502143206417/1000000000000 : ℝ) (502143206427/1000000000000 : ℝ) (502143206381/1000000000000 : ℝ) (502143206391/1000000000000 : ℝ) (502143206399/1000000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 5 (502143206399/1000000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 6 (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16919/131072 : ℝ))) 7 (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16919/131072 : ℝ)) hmem 8 (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16919/131072 : ℝ))) hcmem 8 (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16919/131072 : ℝ)) (49599049439/50000000000 : ℝ) (991980988783/1000000000000 : ℝ) (251071603199/500000000000 : ℝ) (502143206409/1000000000000 : ℝ) (397570474159/500000000000 : ℝ) (795140948339/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1399_exp_lower
  have heNumeric : (256862583351/125000000000 : ℝ)/4 ≤ Real.exp (-10657069626549/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862583351/125000000000 : ℝ)/4 ≤ Real.exp ((8459/65536 : ℝ)-(795140948339/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8459/65536 : ℝ) (16919/131072 : ℝ) (795140948339/1000000000000 : ℝ) (256862583351/125000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1375_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1375_certificate
#check SmaleRate.Proofs.cover8_leaf1376_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1376_certificate
#check SmaleRate.Proofs.cover8_leaf1377_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1377_certificate
#check SmaleRate.Proofs.cover8_leaf1378_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1378_certificate
#check SmaleRate.Proofs.cover8_leaf1379_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1379_certificate
#check SmaleRate.Proofs.cover8_leaf1380_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1380_certificate
#check SmaleRate.Proofs.cover8_leaf1381_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1381_certificate
#check SmaleRate.Proofs.cover8_leaf1382_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1382_certificate
#check SmaleRate.Proofs.cover8_leaf1383_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1383_certificate
#check SmaleRate.Proofs.cover8_leaf1384_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1384_certificate
#check SmaleRate.Proofs.cover8_leaf1385_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1385_certificate
#check SmaleRate.Proofs.cover8_leaf1386_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1386_certificate
#check SmaleRate.Proofs.cover8_leaf1387_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1387_certificate
#check SmaleRate.Proofs.cover8_leaf1388_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1388_certificate
#check SmaleRate.Proofs.cover8_leaf1389_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1389_certificate
#check SmaleRate.Proofs.cover8_leaf1390_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1390_certificate
#check SmaleRate.Proofs.cover8_leaf1391_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1391_certificate
#check SmaleRate.Proofs.cover8_leaf1392_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1392_certificate
#check SmaleRate.Proofs.cover8_leaf1393_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1393_certificate
#check SmaleRate.Proofs.cover8_leaf1394_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1394_certificate
#check SmaleRate.Proofs.cover8_leaf1395_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1395_certificate
#check SmaleRate.Proofs.cover8_leaf1396_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1396_certificate
#check SmaleRate.Proofs.cover8_leaf1397_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1397_certificate
#check SmaleRate.Proofs.cover8_leaf1398_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1398_certificate
#check SmaleRate.Proofs.cover8_leaf1399_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1399_certificate
