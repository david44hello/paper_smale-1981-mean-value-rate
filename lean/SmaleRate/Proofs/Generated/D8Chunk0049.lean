/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1225; no trusted numerical premise.
theorem cover8_leaf1225_exp_radius : (99799583788642831/100000000000000000 : ℝ) ≤ Real.exp ((-16829/1048576 : ℝ)/8) ∧ Real.exp ((-16829/1048576 : ℝ)/8) ≤ (997995837886428311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16829/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1225_exp_lower : (230028347698336391/250000000000000000 : ℝ) ≤ Real.exp ((-42628283223799/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628283223799/64000000000000 : ℝ)/8) ≤ (184022678158669113/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628283223799/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1225_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862564417/125000000000 : ℝ) ≤ 4*Real.exp (33657/262144 : ℝ)*Real.exp (-mu (radius 8 (16829/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862564417/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16829/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1225_exp_radius
  have hrNumeric : (984078720057/1000000000000 : ℝ) ≤ Real.exp (-16829/1048576 : ℝ) ∧ Real.exp (-16829/1048576 : ℝ) ≤ (492039360029/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984078720057/1000000000000 : ℝ) ≤ (radius 8 (16829/131072 : ℝ)) ∧ (radius 8 (16829/131072 : ℝ)) ≤ (492039360029/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16829/131072 : ℝ)) (984078720057/1000000000000 : ℝ) (492039360029/500000000000 : ℝ) (177733150337/1000000000000 : ℝ) (22216643793/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16829/131072 : ℝ)) (984078720057/1000000000000 : ℝ) (492039360029/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984078720057/1000000000000 : ℝ) (492039360029/500000000000 : ℝ) (248009840007/250000000000 : ℝ) (992039360029/1000000000000 : ℝ) (198401483871/200000000000 : ℝ) (992007419357/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 1 (248009840007/250000000000 : ℝ) (992039360029/1000000000000 : ℝ) (198401483871/200000000000 : ℝ) (992007419357/1000000000000 : ℝ) (992023389691/1000000000000 : ℝ) (992023389693/1000000000000 : ℝ) (496011694781/500000000000 : ℝ) (198404677913/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 2 (992023389691/1000000000000 : ℝ) (992023389693/1000000000000 : ℝ) (496011694781/500000000000 : ℝ) (198404677913/200000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 3 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 4 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 5 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 6 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16829/131072 : ℝ)) 7 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16829/131072 : ℝ))) (177733150337/1000000000000 : ℝ) (22216643793/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177733150337/1000000000000 : ℝ) (22216643793/125000000000 : ℝ) (9201040237/15625000000 : ℝ) (147216643793/250000000000 : ℝ) (421584096399/1000000000000 : ℝ) (52698012051/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 1 (9201040237/15625000000 : ℝ) (147216643793/250000000000 : ℝ) (421584096399/1000000000000 : ℝ) (52698012051/125000000000 : ℝ) (505225335783/1000000000000 : ℝ) (50522533579/100000000000 : ℝ) (99650746709/200000000000 : ℝ) (498253733553/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 2 (505225335783/1000000000000 : ℝ) (50522533579/100000000000 : ℝ) (99650746709/200000000000 : ℝ) (498253733553/1000000000000 : ℝ) (62717441833/125000000000 : ℝ) (31358720917/62500000000 : ℝ) (100345485167/200000000000 : ℝ) (501727425843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 3 (62717441833/125000000000 : ℝ) (31358720917/62500000000 : ℝ) (100345485167/200000000000 : ℝ) (501727425843/1000000000000 : ℝ) (501733480249/1000000000000 : ℝ) (250866740129/500000000000 : ℝ) (125433370053/250000000000 : ℝ) (501733480221/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 4 (501733480249/1000000000000 : ℝ) (250866740129/500000000000 : ℝ) (125433370053/250000000000 : ℝ) (501733480221/1000000000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 5 (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 6 (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16829/131072 : ℝ))) 7 (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16829/131072 : ℝ)) hmem 8 (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16829/131072 : ℝ))) hcmem 8 (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16829/131072 : ℝ)) (496011694813/500000000000 : ℝ) (992023389629/1000000000000 : ℝ) (50173348023/100000000000 : ℝ) (6271668503/12500000000 : ℝ) (397229095611/500000000000 : ℝ) (794458191241/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1225_exp_lower
  have heNumeric : (256862564417/125000000000 : ℝ)/4 ≤ Real.exp (-42628283223799/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862564417/125000000000 : ℝ)/4 ≤ Real.exp ((33657/262144 : ℝ)-(794458191241/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33657/262144 : ℝ) (16829/131072 : ℝ) (794458191241/1000000000000 : ℝ) (256862564417/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1226; no trusted numerical premise.
theorem cover8_leaf1226_exp_radius : (498997889200621339/500000000000000000 : ℝ) ≤ Real.exp ((-33659/2097152 : ℝ)/8) ∧ Real.exp ((-33659/2097152 : ℝ)/8) ≤ (997995778401242679/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33659/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1226_exp_lower : (2875354351539361/3125000000000000 : ℝ) ≤ Real.exp ((-21314141139123/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314141139123/32000000000000 : ℝ)/8) ≤ (920113392492595521/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314141139123/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1226_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215642053/31250000000 : ℝ) ≤ 4*Real.exp (16829/131072 : ℝ)*Real.exp (-mu (radius 8 (33659/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (64215642053/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33659/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1226_exp_radius
  have hrNumeric : (246019562703/250000000000 : ℝ) ≤ Real.exp (-33659/2097152 : ℝ) ∧ Real.exp (-33659/2097152 : ℝ) ≤ (984078250813/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246019562703/250000000000 : ℝ) ≤ (radius 8 (33659/262144 : ℝ)) ∧ (radius 8 (33659/262144 : ℝ)) ≤ (984078250813/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33659/262144 : ℝ)) (246019562703/250000000000 : ℝ) (984078250813/1000000000000 : ℝ) (177735748449/1000000000000 : ℝ) (35547149691/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33659/262144 : ℝ)) (246019562703/250000000000 : ℝ) (984078250813/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246019562703/250000000000 : ℝ) (984078250813/1000000000000 : ℝ) (496019562703/500000000000 : ℝ) (992039125407/1000000000000 : ℝ) (496003591421/500000000000 : ℝ) (248001795711/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 1 (496019562703/500000000000 : ℝ) (992039125407/1000000000000 : ℝ) (496003591421/500000000000 : ℝ) (248001795711/250000000000 : ℝ) (248005788531/250000000000 : ℝ) (496011577063/500000000000 : ℝ) (198404630799/200000000000 : ℝ) (992023153997/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 2 (248005788531/250000000000 : ℝ) (496011577063/500000000000 : ℝ) (198404630799/200000000000 : ℝ) (992023153997/1000000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 3 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 4 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 5 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 6 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33659/262144 : ℝ)) 7 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33659/262144 : ℝ))) (177735748449/1000000000000 : ℝ) (35547149691/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177735748449/1000000000000 : ℝ) (35547149691/200000000000 : ℝ) (36804242139/62500000000 : ℝ) (147216968557/250000000000 : ℝ) (105396794439/250000000000 : ℝ) (105396794441/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 1 (36804242139/62500000000 : ℝ) (147216968557/250000000000 : ℝ) (105396794439/250000000000 : ℝ) (105396794441/250000000000 : ℝ) (50522752599/100000000000 : ℝ) (126306881499/250000000000 : ℝ) (498256103991/1000000000000 : ℝ) (498256103999/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 2 (50522752599/100000000000 : ℝ) (126306881499/250000000000 : ℝ) (498256103991/1000000000000 : ℝ) (498256103999/1000000000000 : ℝ) (50174181499/100000000000 : ℝ) (250870907499/500000000000 : ℝ) (501729706843/1000000000000 : ℝ) (501729706851/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 3 (50174181499/100000000000 : ℝ) (250870907499/500000000000 : ℝ) (501729706843/1000000000000 : ℝ) (501729706851/1000000000000 : ℝ) (125433940229/250000000000 : ℝ) (20069430437/40000000000 : ℝ) (501735760879/1000000000000 : ℝ) (62716970111/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 4 (125433940229/250000000000 : ℝ) (20069430437/40000000000 : ℝ) (501735760879/1000000000000 : ℝ) (62716970111/125000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 5 (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 6 (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33659/262144 : ℝ))) 7 (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33659/262144 : ℝ)) hmem 8 (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33659/262144 : ℝ))) hcmem 8 (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33659/262144 : ℝ)) (992023154059/1000000000000 : ℝ) (496011577031/500000000000 : ℝ) (501735760897/1000000000000 : ℝ) (501735760907/1000000000000 : ℝ) (158892398229/200000000000 : ℝ) (198615497791/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1226_exp_lower
  have heNumeric : (64215642053/31250000000 : ℝ)/4 ≤ Real.exp (-21314141139123/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215642053/31250000000 : ℝ)/4 ≤ Real.exp ((16829/131072 : ℝ)-(198615497791/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16829/131072 : ℝ) (33659/262144 : ℝ) (198615497791/250000000000 : ℝ) (64215642053/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1227; no trusted numerical premise.
theorem cover8_leaf1227_exp_radius : (62374732432253787/62500000000000000 : ℝ) ≤ Real.exp ((-8415/524288 : ℝ)/8) ∧ Real.exp ((-8415/524288 : ℝ)/8) ≤ (997995718916060593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8415/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1227_exp_lower : (184022678840048303/200000000000000000 : ℝ) ≤ Real.exp ((-42628281328021/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628281328021/64000000000000 : ℝ)/8) ≤ (230028348550060379/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628281328021/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1227_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450288103/500000000000 : ℝ) ≤ 4*Real.exp (33659/262144 : ℝ)*Real.exp (-mu (radius 8 (8415/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450288103/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8415/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1227_exp_radius
  have hrNumeric : (984077781567/1000000000000 : ℝ) ≤ Real.exp (-8415/524288 : ℝ) ∧ Real.exp (-8415/524288 : ℝ) ≤ (15376215337/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984077781567/1000000000000 : ℝ) ≤ (radius 8 (8415/65536 : ℝ)) ∧ (radius 8 (8415/65536 : ℝ)) ≤ (15376215337/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8415/65536 : ℝ)) (984077781567/1000000000000 : ℝ) (15376215337/15625000000 : ℝ) (177738346521/1000000000000 : ℝ) (5554323329/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8415/65536 : ℝ)) (984077781567/1000000000000 : ℝ) (15376215337/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984077781567/1000000000000 : ℝ) (15376215337/15625000000 : ℝ) (992038890783/1000000000000 : ℝ) (31001215337/31250000000 : ℝ) (99200694633/100000000000 : ℝ) (992006946331/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 1 (992038890783/1000000000000 : ℝ) (31001215337/31250000000 : ℝ) (99200694633/100000000000 : ℝ) (992006946331/1000000000000 : ℝ) (248005729639/250000000000 : ℝ) (496011459279/500000000000 : ℝ) (992022918427/1000000000000 : ℝ) (992022918429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 2 (248005729639/250000000000 : ℝ) (496011459279/500000000000 : ℝ) (992022918427/1000000000000 : ℝ) (992022918429/1000000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 3 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 4 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 5 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 6 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8415/65536 : ℝ)) 7 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8415/65536 : ℝ))) (177738346521/1000000000000 : ℝ) (5554323329/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177738346521/1000000000000 : ℝ) (5554323329/31250000000 : ℝ) (29443458663/50000000000 : ℝ) (36804323329/62500000000 : ℝ) (105397564761/250000000000 : ℝ) (421590259053/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 1 (29443458663/50000000000 : ℝ) (36804323329/62500000000 : ℝ) (105397564761/250000000000 : ℝ) (421590259053/1000000000000 : ℝ) (63153714519/125000000000 : ℝ) (505229716159/1000000000000 : ℝ) (249129237193/500000000000 : ℝ) (249129237197/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 2 (63153714519/125000000000 : ℝ) (505229716159/1000000000000 : ℝ) (249129237193/500000000000 : ℝ) (249129237197/500000000000 : ℝ) (501744095269/1000000000000 : ℝ) (501744095277/1000000000000 : ℝ) (250865993901/500000000000 : ℝ) (501731987811/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 3 (501744095269/1000000000000 : ℝ) (501744095277/1000000000000 : ℝ) (250865993901/500000000000 : ℝ) (501731987811/1000000000000 : ℝ) (100347608307/200000000000 : ℝ) (62717255193/125000000000 : ℝ) (250869020749/500000000000 : ℝ) (125434510377/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 4 (100347608307/200000000000 : ℝ) (62717255193/125000000000 : ℝ) (250869020749/500000000000 : ℝ) (125434510377/250000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 5 (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 6 (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8415/65536 : ℝ))) 7 (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8415/65536 : ℝ)) hmem 8 (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8415/65536 : ℝ))) hcmem 8 (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8415/65536 : ℝ)) (992022918491/1000000000000 : ℝ) (496011459247/500000000000 : ℝ) (125434510379/250000000000 : ℝ) (250869020763/500000000000 : ℝ) (158893158199/200000000000 : ℝ) (397232895507/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1227_exp_lower
  have heNumeric : (1027450288103/500000000000 : ℝ)/4 ≤ Real.exp (-42628281328021/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450288103/500000000000 : ℝ)/4 ≤ Real.exp ((33659/262144 : ℝ)-(397232895507/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33659/262144 : ℝ) (8415/65536 : ℝ) (397232895507/500000000000 : ℝ) (1027450288103/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1228; no trusted numerical premise.
theorem cover8_leaf1228_exp_radius : (249498914857720513/250000000000000000 : ℝ) ≤ Real.exp ((-33661/2097152 : ℝ)/8) ∧ Real.exp ((-33661/2097152 : ℝ)/8) ≤ (997995659430882053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33661/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1228_exp_lower : (920113395917548703/1000000000000000000 : ℝ) ≤ Real.exp ((-2131414018621/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131414018621/3200000000000 : ℝ)/8) ≤ (28753543622423397/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131414018621/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1228_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862575861/125000000000 : ℝ) ≤ 4*Real.exp (8415/65536 : ℝ)*Real.exp (-mu (radius 8 (33661/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862575861/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33661/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1228_exp_radius
  have hrNumeric : (984077312323/1000000000000 : ℝ) ≤ Real.exp (-33661/2097152 : ℝ) ∧ Real.exp (-33661/2097152 : ℝ) ≤ (246019328081/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984077312323/1000000000000 : ℝ) ≤ (radius 8 (33661/262144 : ℝ)) ∧ (radius 8 (33661/262144 : ℝ)) ≤ (246019328081/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33661/262144 : ℝ)) (984077312323/1000000000000 : ℝ) (246019328081/250000000000 : ℝ) (177740944549/1000000000000 : ℝ) (35548188911/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33661/262144 : ℝ)) (984077312323/1000000000000 : ℝ) (246019328081/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984077312323/1000000000000 : ℝ) (246019328081/250000000000 : ℝ) (992038656161/1000000000000 : ℝ) (496019328081/500000000000 : ℝ) (992006709817/1000000000000 : ℝ) (992006709819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 1 (992038656161/1000000000000 : ℝ) (496019328081/500000000000 : ℝ) (992006709817/1000000000000 : ℝ) (992006709819/1000000000000 : ℝ) (992022682989/1000000000000 : ℝ) (992022682991/1000000000000 : ℝ) (49601134143/50000000000 : ℝ) (496011341431/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 2 (992022682989/1000000000000 : ℝ) (992022682991/1000000000000 : ℝ) (49601134143/50000000000 : ℝ) (496011341431/500000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 3 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 4 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 5 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 6 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33661/262144 : ℝ)) 7 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33661/262144 : ℝ))) (177740944549/1000000000000 : ℝ) (35548188911/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177740944549/1000000000000 : ℝ) (35548188911/200000000000 : ℝ) (294435236137/500000000000 : ℝ) (294435236139/500000000000 : ℝ) (13174791883/31250000000 : ℝ) (84318668053/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 1 (294435236137/500000000000 : ℝ) (294435236139/500000000000 : ℝ) (13174791883/31250000000 : ℝ) (84318668053/200000000000 : ℝ) (101046381253/200000000000 : ℝ) (15788497071/31250000000 : ℝ) (498260844723/1000000000000 : ℝ) (498260844731/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 2 (101046381253/200000000000 : ℝ) (15788497071/31250000000 : ℝ) (498260844723/1000000000000 : ℝ) (498260844731/1000000000000 : ℝ) (250873187747/500000000000 : ℝ) (250873187751/500000000000 : ℝ) (125433567177/250000000000 : ℝ) (501734268717/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 3 (250873187747/500000000000 : ℝ) (250873187751/500000000000 : ℝ) (125433567177/250000000000 : ℝ) (501734268717/1000000000000 : ℝ) (501740322101/1000000000000 : ℝ) (50174032211/100000000000 : ℝ) (31358770129/62500000000 : ℝ) (501740322073/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 4 (501740322101/1000000000000 : ℝ) (50174032211/100000000000 : ℝ) (31358770129/62500000000 : ℝ) (501740322073/1000000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 5 (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 6 (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33661/262144 : ℝ))) 7 (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33661/262144 : ℝ)) hmem 8 (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33661/262144 : ℝ))) hcmem 8 (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33661/262144 : ℝ)) (248005670731/250000000000 : ℝ) (992022682927/1000000000000 : ℝ) (250870161041/500000000000 : ℝ) (125435080523/250000000000 : ℝ) (794469590761/1000000000000 : ℝ) (39723479539/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1228_exp_lower
  have heNumeric : (256862575861/125000000000 : ℝ)/4 ≤ Real.exp (-2131414018621/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862575861/125000000000 : ℝ)/4 ≤ Real.exp ((8415/65536 : ℝ)-(39723479539/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8415/65536 : ℝ) (33661/262144 : ℝ) (39723479539/50000000000 : ℝ) (256862575861/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1229; no trusted numerical premise.
theorem cover8_leaf1229_exp_radius : (997995599945707057/1000000000000000000 : ℝ) ≤ Real.exp ((-16831/1048576 : ℝ)/8) ∧ Real.exp ((-16831/1048576 : ℝ)/8) ≤ (498997799972853529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16831/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1229_exp_lower : (920113397642676859/1000000000000000000 : ℝ) ≤ Real.exp ((-42628279412467/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628279412467/64000000000000 : ℝ)/8) ≤ (46005669882133843/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628279412467/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1229_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490063771/100000000000 : ℝ) ≤ 4*Real.exp (33661/262144 : ℝ)*Real.exp (-mu (radius 8 (16831/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490063771/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16831/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1229_exp_radius
  have hrNumeric : (492038421539/500000000000 : ℝ) ≤ Real.exp (-16831/1048576 : ℝ) ∧ Real.exp (-16831/1048576 : ℝ) ≤ (984076843079/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492038421539/500000000000 : ℝ) ≤ (radius 8 (16831/131072 : ℝ)) ∧ (radius 8 (16831/131072 : ℝ)) ≤ (984076843079/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16831/131072 : ℝ)) (492038421539/500000000000 : ℝ) (984076843079/1000000000000 : ℝ) (88871771271/500000000000 : ℝ) (177743542549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16831/131072 : ℝ)) (492038421539/500000000000 : ℝ) (984076843079/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492038421539/500000000000 : ℝ) (984076843079/1000000000000 : ℝ) (992038421539/1000000000000 : ℝ) (49601921077/50000000000 : ℝ) (124000809163/125000000000 : ℝ) (198401294661/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 1 (992038421539/1000000000000 : ℝ) (49601921077/50000000000 : ℝ) (124000809163/125000000000 : ℝ) (198401294661/200000000000 : ℝ) (992022447421/1000000000000 : ℝ) (992022447423/1000000000000 : ℝ) (248005611823/250000000000 : ℝ) (496011223647/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 2 (992022447421/1000000000000 : ℝ) (992022447423/1000000000000 : ℝ) (248005611823/250000000000 : ℝ) (496011223647/500000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 3 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 4 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 5 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 6 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16831/131072 : ℝ)) 7 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16831/131072 : ℝ))) (88871771271/500000000000 : ℝ) (177743542549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88871771271/500000000000 : ℝ) (177743542549/1000000000000 : ℝ) (588871771271/1000000000000 : ℝ) (23554870851/40000000000 : ℝ) (84319284281/200000000000 : ℝ) (210798210707/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 1 (588871771271/1000000000000 : ℝ) (23554870851/40000000000 : ℝ) (84319284281/200000000000 : ℝ) (210798210707/500000000000 : ℝ) (252617048169/500000000000 : ℝ) (101046819269/200000000000 : ℝ) (124565803753/250000000000 : ℝ) (24913160751/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 2 (252617048169/500000000000 : ℝ) (101046819269/200000000000 : ℝ) (124565803753/250000000000 : ℝ) (24913160751/50000000000 : ℝ) (20069946227/40000000000 : ℝ) (501748655683/1000000000000 : ℝ) (50173654957/100000000000 : ℝ) (501736549579/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 3 (20069946227/40000000000 : ℝ) (501748655683/1000000000000 : ℝ) (50173654957/100000000000 : ℝ) (501736549579/1000000000000 : ℝ) (250871301311/500000000000 : ℝ) (501742602631/1000000000000 : ℝ) (100348520517/200000000000 : ℝ) (100348520519/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 4 (250871301311/500000000000 : ℝ) (501742602631/1000000000000 : ℝ) (100348520517/200000000000 : ℝ) (100348520519/200000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 5 (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 6 (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16831/131072 : ℝ))) 7 (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16831/131072 : ℝ)) hmem 8 (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16831/131072 : ℝ))) hcmem 8 (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16831/131072 : ℝ)) (248005611839/250000000000 : ℝ) (992022447359/1000000000000 : ℝ) (501742602603/1000000000000 : ℝ) (501742602613/1000000000000 : ℝ) (794473390459/1000000000000 : ℝ) (397236695239/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1229_exp_lower
  have heNumeric : (205490063771/100000000000 : ℝ)/4 ≤ Real.exp (-42628279412467/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490063771/100000000000 : ℝ)/4 ≤ Real.exp ((33661/262144 : ℝ)-(397236695239/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33661/262144 : ℝ) (16831/131072 : ℝ) (397236695239/500000000000 : ℝ) (205490063771/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1230; no trusted numerical premise.
theorem cover8_leaf1230_exp_radius : (997995540460535607/1000000000000000000 : ℝ) ≤ Real.exp ((-33663/2097152 : ℝ)/8) ∧ Real.exp ((-33663/2097152 : ℝ)/8) ≤ (124749442557566951/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33663/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1230_exp_lower : (184022679875424233/200000000000000000 : ℝ) ≤ Real.exp ((-4262827844733/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262827844733/6400000000000 : ℝ)/8) ≤ (460056699688560583/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262827844733/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1230_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450334349/500000000000 : ℝ) ≤ 4*Real.exp (16831/131072 : ℝ)*Real.exp (-mu (radius 8 (33663/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450334349/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33663/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1230_exp_radius
  have hrNumeric : (492038186917/500000000000 : ℝ) ≤ Real.exp (-33663/2097152 : ℝ) ∧ Real.exp (-33663/2097152 : ℝ) ≤ (196815274767/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492038186917/500000000000 : ℝ) ≤ (radius 8 (33663/262144 : ℝ)) ∧ (radius 8 (33663/262144 : ℝ)) ≤ (196815274767/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33663/262144 : ℝ)) (492038186917/500000000000 : ℝ) (196815274767/200000000000 : ℝ) (177746140491/1000000000000 : ℝ) (88873070249/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33663/262144 : ℝ)) (492038186917/500000000000 : ℝ) (196815274767/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492038186917/500000000000 : ℝ) (196815274767/200000000000 : ℝ) (992038186917/1000000000000 : ℝ) (496019093459/500000000000 : ℝ) (992006236791/1000000000000 : ℝ) (992006236793/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 1 (992038186917/1000000000000 : ℝ) (496019093459/500000000000 : ℝ) (992006236791/1000000000000 : ℝ) (992006236793/1000000000000 : ℝ) (496011105927/500000000000 : ℝ) (62001388241/62500000000 : ℝ) (39680888469/40000000000 : ℝ) (992022211727/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 2 (496011105927/500000000000 : ℝ) (62001388241/62500000000 : ℝ) (39680888469/40000000000 : ℝ) (992022211727/1000000000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 3 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 4 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 5 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 6 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33663/262144 : ℝ)) 7 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33663/262144 : ℝ))) (177746140491/1000000000000 : ℝ) (88873070249/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177746140491/1000000000000 : ℝ) (88873070249/500000000000 : ℝ) (117774614049/200000000000 : ℝ) (588873070249/1000000000000 : ℝ) (421599502479/1000000000000 : ℝ) (52699937811/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 1 (117774614049/200000000000 : ℝ) (588873070249/1000000000000 : ℝ) (421599502479/1000000000000 : ℝ) (52699937811/125000000000 : ℝ) (252618143181/500000000000 : ℝ) (505236286369/1000000000000 : ℝ) (124566396311/250000000000 : ℝ) (124566396313/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 2 (252618143181/500000000000 : ℝ) (505236286369/1000000000000 : ℝ) (124566396311/250000000000 : ℝ) (124566396313/250000000000 : ℝ) (501750935803/1000000000000 : ℝ) (501750935811/1000000000000 : ℝ) (501738830379/1000000000000 : ℝ) (125434707597/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 3 (501750935803/1000000000000 : ℝ) (501750935811/1000000000000 : ℝ) (501738830379/1000000000000 : ℝ) (125434707597/250000000000 : ℝ) (501744883091/1000000000000 : ℝ) (5017448831/10000000000 : ℝ) (250872441527/500000000000 : ℝ) (501744883063/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 4 (501744883091/1000000000000 : ℝ) (5017448831/10000000000 : ℝ) (250872441527/500000000000 : ℝ) (501744883063/1000000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 5 (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 6 (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33663/262144 : ℝ))) 7 (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33663/262144 : ℝ)) hmem 8 (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33663/262144 : ℝ))) hcmem 8 (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33663/262144 : ℝ)) (992022211789/1000000000000 : ℝ) (62001388237/62500000000 : ℝ) (3919881899/7812500000 : ℝ) (250872441541/500000000000 : ℝ) (198619297519/250000000000 : ℝ) (158895438019/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1230_exp_lower
  have heNumeric : (1027450334349/500000000000 : ℝ)/4 ≤ Real.exp (-4262827844733/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450334349/500000000000 : ℝ)/4 ≤ Real.exp ((16831/131072 : ℝ)-(158895438019/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16831/131072 : ℝ) (33663/262144 : ℝ) (158895438019/200000000000 : ℝ) (1027450334349/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1231; no trusted numerical premise.
theorem cover8_leaf1231_exp_radius : (997995480975367703/1000000000000000000 : ℝ) ≤ Real.exp ((-263/16384 : ℝ)/8) ∧ Real.exp ((-263/16384 : ℝ)/8) ≤ (124749435121920963/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-263/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1231_exp_lower : (920113401120306553/1000000000000000000 : ℝ) ≤ Real.exp ((-42628277477329/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628277477329/64000000000000 : ℝ)/8) ≤ (460056700560153277/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628277477329/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1231_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900699843/1000000000000 : ℝ) ≤ 4*Real.exp (33663/262144 : ℝ)*Real.exp (-mu (radius 8 (263/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900699843/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (263/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1231_exp_radius
  have hrNumeric : (98407590459/100000000000 : ℝ) ≤ Real.exp (-263/16384 : ℝ) ∧ Real.exp (-263/16384 : ℝ) ≤ (984075904591/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98407590459/100000000000 : ℝ) ≤ (radius 8 (263/2048 : ℝ)) ∧ (radius 8 (263/2048 : ℝ)) ≤ (984075904591/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (263/2048 : ℝ)) (98407590459/100000000000 : ℝ) (984075904591/1000000000000 : ℝ) (177748738401/1000000000000 : ℝ) (22218592301/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (263/2048 : ℝ)) (98407590459/100000000000 : ℝ) (984075904591/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (263/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98407590459/100000000000 : ℝ) (984075904591/1000000000000 : ℝ) (198407590459/200000000000 : ℝ) (124004744037/125000000000 : ℝ) (992006000279/1000000000000 : ℝ) (24800150007/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (263/2048 : ℝ)) 1 (198407590459/200000000000 : ℝ) (124004744037/125000000000 : ℝ) (992006000279/1000000000000 : ℝ) (24800150007/25000000000 : ℝ) (992021976287/1000000000000 : ℝ) (31000686759/31250000000 : ℝ) (496010988079/500000000000 : ℝ) (6200137351/6250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (263/2048 : ℝ)) 2 (992021976287/1000000000000 : ℝ) (31000686759/31250000000 : ℝ) (496010988079/500000000000 : ℝ) (6200137351/6250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (263/2048 : ℝ)) 3 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (263/2048 : ℝ)) 4 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (263/2048 : ℝ)) 5 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (263/2048 : ℝ)) 6 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (263/2048 : ℝ)) 7 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (263/2048 : ℝ))) (177748738401/1000000000000 : ℝ) (22218592301/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177748738401/1000000000000 : ℝ) (22218592301/125000000000 : ℝ) (1472185923/2500000000 : ℝ) (147218592301/250000000000 : ℝ) (105400645871/250000000000 : ℝ) (210801291747/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 1 (1472185923/2500000000 : ℝ) (147218592301/250000000000 : ℝ) (105400645871/250000000000 : ℝ) (210801291747/500000000000 : ℝ) (252619238171/500000000000 : ℝ) (505238476349/1000000000000 : ℝ) (498267955423/1000000000000 : ℝ) (62283494429/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 2 (252619238171/500000000000 : ℝ) (505238476349/1000000000000 : ℝ) (498267955423/1000000000000 : ℝ) (62283494429/125000000000 : ℝ) (250876607941/500000000000 : ℝ) (501753215891/1000000000000 : ℝ) (501741111139/1000000000000 : ℝ) (125435277787/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 3 (250876607941/500000000000 : ℝ) (501753215891/1000000000000 : ℝ) (501741111139/1000000000000 : ℝ) (125435277787/250000000000 : ℝ) (50174716351/100000000000 : ℝ) (783979943/1562500000 : ℝ) (501747163473/1000000000000 : ℝ) (501747163483/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 4 (50174716351/100000000000 : ℝ) (783979943/1562500000 : ℝ) (501747163473/1000000000000 : ℝ) (501747163483/1000000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 5 (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 6 (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (263/2048 : ℝ))) 7 (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (263/2048 : ℝ)) hmem 8 (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (263/2048 : ℝ))) hcmem 8 (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (263/2048 : ℝ)) (496010988111/500000000000 : ℝ) (31000686757/31250000000 : ℝ) (501747163491/1000000000000 : ℝ) (250873581751/500000000000 : ℝ) (49655061851/62500000000 : ℝ) (198620247409/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1231_exp_lower
  have heNumeric : (2054900699843/1000000000000 : ℝ)/4 ≤ Real.exp (-42628277477329/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900699843/1000000000000 : ℝ)/4 ≤ Real.exp ((33663/262144 : ℝ)-(198620247409/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33663/262144 : ℝ) (263/2048 : ℝ) (198620247409/250000000000 : ℝ) (2054900699843/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1232; no trusted numerical premise.
theorem cover8_leaf1232_exp_radius : (199599084298040669/200000000000000000 : ℝ) ≤ Real.exp ((-33665/2097152 : ℝ)/8) ∧ Real.exp ((-33665/2097152 : ℝ)/8) ≤ (498997710745101673/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33665/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1232_exp_lower : (920113402872233021/1000000000000000000 : ℝ) ≤ Real.exp ((-666066820351/1000000000000 : ℝ)/8) ∧ Real.exp ((-666066820351/1000000000000 : ℝ)/8) ≤ (460056701436116511/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666066820351/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1232_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862591393/125000000000 : ℝ) ≤ 4*Real.exp (263/2048 : ℝ)*Real.exp (-mu (radius 8 (33665/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862591393/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33665/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1232_exp_radius
  have hrNumeric : (492037717673/500000000000 : ℝ) ≤ Real.exp (-33665/2097152 : ℝ) ∧ Real.exp (-33665/2097152 : ℝ) ≤ (984075435347/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492037717673/500000000000 : ℝ) ≤ (radius 8 (33665/262144 : ℝ)) ∧ (radius 8 (33665/262144 : ℝ)) ≤ (984075435347/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33665/262144 : ℝ)) (492037717673/500000000000 : ℝ) (984075435347/1000000000000 : ℝ) (11109458517/62500000000 : ℝ) (88875668139/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33665/262144 : ℝ)) (492037717673/500000000000 : ℝ) (984075435347/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492037717673/500000000000 : ℝ) (984075435347/1000000000000 : ℝ) (992037717673/1000000000000 : ℝ) (496018858837/500000000000 : ℝ) (496002881883/500000000000 : ℝ) (124000720471/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 1 (992037717673/1000000000000 : ℝ) (496018858837/500000000000 : ℝ) (496002881883/500000000000 : ℝ) (124000720471/125000000000 : ℝ) (992021740719/1000000000000 : ℝ) (992021740721/1000000000000 : ℝ) (99202174059/100000000000 : ℝ) (992021740593/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 2 (992021740719/1000000000000 : ℝ) (992021740721/1000000000000 : ℝ) (99202174059/100000000000 : ℝ) (992021740593/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 3 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 4 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 5 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 6 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33665/262144 : ℝ)) 7 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33665/262144 : ℝ))) (11109458517/62500000000 : ℝ) (88875668139/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11109458517/62500000000 : ℝ) (88875668139/500000000000 : ℝ) (73609458517/125000000000 : ℝ) (588875668139/1000000000000 : ℝ) (421605664421/1000000000000 : ℝ) (421605664429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 1 (73609458517/125000000000 : ℝ) (588875668139/1000000000000 : ℝ) (421605664421/1000000000000 : ℝ) (421605664429/1000000000000 : ℝ) (252620333139/500000000000 : ℝ) (126310166571/250000000000 : ℝ) (31141895347/62500000000 : ℝ) (498270325559/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 2 (252620333139/500000000000 : ℝ) (126310166571/250000000000 : ℝ) (31141895347/62500000000 : ℝ) (498270325559/1000000000000 : ℝ) (100351099183/200000000000 : ℝ) (250877747961/500000000000 : ℝ) (501743391853/1000000000000 : ℝ) (25087169593/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 3 (100351099183/200000000000 : ℝ) (250877747961/500000000000 : ℝ) (501743391853/1000000000000 : ℝ) (25087169593/50000000000 : ℝ) (125437360971/250000000000 : ℝ) (501749443891/1000000000000 : ℝ) (501749443847/1000000000000 : ℝ) (100349888771/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 4 (125437360971/250000000000 : ℝ) (501749443891/1000000000000 : ℝ) (501749443847/1000000000000 : ℝ) (100349888771/200000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 5 (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 6 (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33665/262144 : ℝ))) 7 (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33665/262144 : ℝ)) hmem 8 (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33665/262144 : ℝ))) hcmem 8 (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33665/262144 : ℝ)) (496010870327/500000000000 : ℝ) (992021740657/1000000000000 : ℝ) (100349888773/200000000000 : ℝ) (501749443873/1000000000000 : ℝ) (158896957817/200000000000 : ℝ) (794484789101/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1232_exp_lower
  have heNumeric : (256862591393/125000000000 : ℝ)/4 ≤ Real.exp (-666066820351/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862591393/125000000000 : ℝ)/4 ≤ Real.exp ((263/2048 : ℝ)-(794484789101/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (263/2048 : ℝ) (33665/262144 : ℝ) (794484789101/1000000000000 : ℝ) (256862591393/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1233; no trusted numerical premise.
theorem cover8_leaf1233_exp_radius : (997995362005042533/1000000000000000000 : ℝ) ≤ Real.exp ((-16833/1048576 : ℝ)/8) ∧ Real.exp ((-16833/1048576 : ℝ)/8) ≤ (498997681002521267/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16833/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1233_exp_lower : (920113404632440513/1000000000000000000 : ℝ) ≤ Real.exp ((-42628275522991/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628275522991/64000000000000 : ℝ)/8) ≤ (460056702316220257/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628275522991/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1233_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215648831/31250000000 : ℝ) ≤ 4*Real.exp (33665/262144 : ℝ)*Real.exp (-mu (radius 8 (16833/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215648831/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16833/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1233_exp_radius
  have hrNumeric : (492037483051/500000000000 : ℝ) ≤ Real.exp (-16833/1048576 : ℝ) ∧ Real.exp (-16833/1048576 : ℝ) ≤ (984074966103/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492037483051/500000000000 : ℝ) ≤ (radius 8 (16833/131072 : ℝ)) ∧ (radius 8 (16833/131072 : ℝ)) ≤ (984074966103/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16833/131072 : ℝ)) (492037483051/500000000000 : ℝ) (984074966103/1000000000000 : ℝ) (177753934103/1000000000000 : ℝ) (17775393411/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16833/131072 : ℝ)) (492037483051/500000000000 : ℝ) (984074966103/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492037483051/500000000000 : ℝ) (984074966103/1000000000000 : ℝ) (992037483051/1000000000000 : ℝ) (248009370763/250000000000 : ℝ) (992005527253/1000000000000 : ℝ) (198401105451/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 1 (992037483051/1000000000000 : ℝ) (248009370763/250000000000 : ℝ) (992005527253/1000000000000 : ℝ) (198401105451/200000000000 : ℝ) (7750168009/7812500000 : ℝ) (496010752577/500000000000 : ℝ) (992021505023/1000000000000 : ℝ) (39680860201/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 2 (7750168009/7812500000 : ℝ) (496010752577/500000000000 : ℝ) (992021505023/1000000000000 : ℝ) (39680860201/40000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 3 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 4 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 5 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 6 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16833/131072 : ℝ)) 7 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16833/131072 : ℝ))) (177753934103/1000000000000 : ℝ) (17775393411/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177753934103/1000000000000 : ℝ) (17775393411/100000000000 : ℝ) (588876967051/1000000000000 : ℝ) (117775393411/200000000000 : ℝ) (421608745287/1000000000000 : ℝ) (26350546581/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 1 (588876967051/1000000000000 : ℝ) (117775393411/200000000000 : ℝ) (421608745287/1000000000000 : ℝ) (26350546581/62500000000 : ℝ) (505242856169/1000000000000 : ℝ) (31577678511/62500000000 : ℝ) (249136347813/500000000000 : ℝ) (249136347817/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 2 (505242856169/1000000000000 : ℝ) (31577678511/62500000000 : ℝ) (249136347813/500000000000 : ℝ) (249136347817/500000000000 : ℝ) (501757775897/1000000000000 : ℝ) (100351555181/200000000000 : ℝ) (125436418129/250000000000 : ℝ) (20069826901/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 3 (501757775897/1000000000000 : ℝ) (100351555181/200000000000 : ℝ) (125436418129/250000000000 : ℝ) (20069826901/40000000000 : ℝ) (250875862103/500000000000 : ℝ) (100350344843/200000000000 : ℝ) (50175172417/100000000000 : ℝ) (501751724179/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 4 (250875862103/500000000000 : ℝ) (100350344843/200000000000 : ℝ) (50175172417/100000000000 : ℝ) (501751724179/1000000000000 : ℝ) (125437931047/250000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 5 (125437931047/250000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 6 (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16833/131072 : ℝ))) 7 (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16833/131072 : ℝ)) hmem 8 (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16833/131072 : ℝ))) hcmem 8 (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16833/131072 : ℝ)) (992021505087/1000000000000 : ℝ) (99202150509/100000000000 : ℝ) (501751724187/1000000000000 : ℝ) (501751724197/1000000000000 : ℝ) (31779543539/40000000000 : ℝ) (397244294247/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1233_exp_lower
  have heNumeric : (64215648831/31250000000 : ℝ)/4 ≤ Real.exp (-42628275522991/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215648831/31250000000 : ℝ)/4 ≤ Real.exp ((33665/262144 : ℝ)-(397244294247/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33665/262144 : ℝ) (16833/131072 : ℝ) (397244294247/500000000000 : ℝ) (64215648831/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1234; no trusted numerical premise.
theorem cover8_leaf1234_exp_radius : (498997651259942633/500000000000000000 : ℝ) ≤ Real.exp ((-33667/2097152 : ℝ)/8) ∧ Real.exp ((-33667/2097152 : ℝ)/8) ≤ (997995302519885267/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33667/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1234_exp_lower : (184022681280438837/200000000000000000 : ℝ) ≤ Real.exp ((-21314137269103/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314137269103/32000000000000 : ℝ)/8) ≤ (460056703201097093/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314137269103/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1234_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725198553/250000000000 : ℝ) ≤ 4*Real.exp (16833/131072 : ℝ)*Real.exp (-mu (radius 8 (33667/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725198553/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33667/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1234_exp_radius
  have hrNumeric : (984074496859/1000000000000 : ℝ) ≤ Real.exp (-33667/2097152 : ℝ) ∧ Real.exp (-33667/2097152 : ℝ) ≤ (49203724843/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984074496859/1000000000000 : ℝ) ≤ (radius 8 (33667/262144 : ℝ)) ∧ (radius 8 (33667/262144 : ℝ)) ≤ (49203724843/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33667/262144 : ℝ)) (984074496859/1000000000000 : ℝ) (49203724843/50000000000 : ℝ) (17775653189/100000000000 : ℝ) (177756531897/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33667/262144 : ℝ)) (984074496859/1000000000000 : ℝ) (49203724843/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984074496859/1000000000000 : ℝ) (49203724843/50000000000 : ℝ) (992037248429/1000000000000 : ℝ) (99203724843/100000000000 : ℝ) (992005290741/1000000000000 : ℝ) (496002645371/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 1 (992037248429/1000000000000 : ℝ) (99203724843/100000000000 : ℝ) (992005290741/1000000000000 : ℝ) (496002645371/500000000000 : ℝ) (198404253917/200000000000 : ℝ) (496010634793/500000000000 : ℝ) (62001329341/62500000000 : ℝ) (496010634729/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 2 (198404253917/200000000000 : ℝ) (496010634793/500000000000 : ℝ) (62001329341/62500000000 : ℝ) (496010634729/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 3 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 4 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 5 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 6 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33667/262144 : ℝ)) 7 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33667/262144 : ℝ))) (17775653189/100000000000 : ℝ) (177756531897/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17775653189/100000000000 : ℝ) (177756531897/1000000000000 : ℝ) (117775653189/200000000000 : ℝ) (588878265949/1000000000000 : ℝ) (421611826079/1000000000000 : ℝ) (52701478261/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 1 (117775653189/200000000000 : ℝ) (588878265949/1000000000000 : ℝ) (421611826079/1000000000000 : ℝ) (52701478261/125000000000 : ℝ) (126311261503/250000000000 : ℝ) (505245046019/1000000000000 : ℝ) (124568766411/250000000000 : ℝ) (124568766413/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 2 (126311261503/250000000000 : ℝ) (505245046019/1000000000000 : ℝ) (124568766411/250000000000 : ℝ) (124568766413/250000000000 : ℝ) (125440013957/250000000000 : ℝ) (125440013959/250000000000 : ℝ) (501747953127/1000000000000 : ℝ) (31359247071/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 3 (125440013957/250000000000 : ℝ) (125440013959/250000000000 : ℝ) (501747953127/1000000000000 : ℝ) (31359247071/62500000000 : ℝ) (501754004477/1000000000000 : ℝ) (250877002243/500000000000 : ℝ) (501754004441/1000000000000 : ℝ) (10035080089/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 4 (501754004477/1000000000000 : ℝ) (250877002243/500000000000 : ℝ) (501754004441/1000000000000 : ℝ) (10035080089/20000000000 : ℝ) (501754004459/1000000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 5 (501754004459/1000000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 6 (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33667/262144 : ℝ))) 7 (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33667/262144 : ℝ)) hmem 8 (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33667/262144 : ℝ))) hcmem 8 (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33667/262144 : ℝ)) (12400265869/12500000000 : ℝ) (496010634761/500000000000 : ℝ) (250877002229/500000000000 : ℝ) (125438501117/250000000000 : ℝ) (397246193893/500000000000 : ℝ) (198623096951/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1234_exp_lower
  have heNumeric : (513725198553/250000000000 : ℝ)/4 ≤ Real.exp (-21314137269103/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725198553/250000000000 : ℝ)/4 ≤ Real.exp ((16833/131072 : ℝ)-(198623096951/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16833/131072 : ℝ) (33667/262144 : ℝ) (198623096951/250000000000 : ℝ) (513725198553/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1235; no trusted numerical premise.
theorem cover8_leaf1235_exp_radius : (124749405379341443/125000000000000000 : ℝ) ≤ Real.exp ((-8417/524288 : ℝ)/8) ∧ Real.exp ((-8417/524288 : ℝ)/8) ≤ (199599048606946309/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8417/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1235_exp_lower : (57507088011300247/62500000000000000 : ℝ) ≤ Real.exp ((-42628273548493/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628273548493/64000000000000 : ℝ)/8) ≤ (920113408180803953/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628273548493/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1235_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900825989/1000000000000 : ℝ) ≤ 4*Real.exp (33667/262144 : ℝ)*Real.exp (-mu (radius 8 (8417/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900825989/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8417/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1235_exp_radius
  have hrNumeric : (30752313363/31250000000 : ℝ) ≤ Real.exp (-8417/524288 : ℝ) ∧ Real.exp (-8417/524288 : ℝ) ≤ (984074027617/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30752313363/31250000000 : ℝ) ≤ (radius 8 (8417/65536 : ℝ)) ∧ (radius 8 (8417/65536 : ℝ)) ≤ (984074027617/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8417/65536 : ℝ)) (30752313363/31250000000 : ℝ) (984074027617/1000000000000 : ℝ) (177759129637/1000000000000 : ℝ) (44439782411/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8417/65536 : ℝ)) (30752313363/31250000000 : ℝ) (984074027617/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30752313363/31250000000 : ℝ) (984074027617/1000000000000 : ℝ) (62002313363/62500000000 : ℝ) (992037013809/1000000000000 : ℝ) (992005054229/1000000000000 : ℝ) (99200505423/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 1 (62002313363/62500000000 : ℝ) (992037013809/1000000000000 : ℝ) (992005054229/1000000000000 : ℝ) (99200505423/100000000000 : ℝ) (496010517009/500000000000 : ℝ) (49601051701/50000000000 : ℝ) (992021033889/1000000000000 : ℝ) (992021033891/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 2 (496010517009/500000000000 : ℝ) (49601051701/50000000000 : ℝ) (992021033889/1000000000000 : ℝ) (992021033891/1000000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 3 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 4 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 5 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 6 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8417/65536 : ℝ)) 7 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8417/65536 : ℝ))) (177759129637/1000000000000 : ℝ) (44439782411/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177759129637/1000000000000 : ℝ) (44439782411/250000000000 : ℝ) (294439782409/500000000000 : ℝ) (294439782411/500000000000 : ℝ) (421614906801/1000000000000 : ℝ) (42161490681/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 1 (294439782409/500000000000 : ℝ) (294439782411/500000000000 : ℝ) (421614906801/1000000000000 : ℝ) (42161490681/100000000000 : ℝ) (505247235809/1000000000000 : ℝ) (63155904477/125000000000 : ℝ) (498277435609/1000000000000 : ℝ) (498277435617/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 2 (505247235809/1000000000000 : ℝ) (63155904477/125000000000 : ℝ) (498277435609/1000000000000 : ℝ) (498277435617/1000000000000 : ℝ) (501762335709/1000000000000 : ℝ) (501762335717/1000000000000 : ℝ) (501750233689/1000000000000 : ℝ) (501750233697/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 3 (501762335709/1000000000000 : ℝ) (501762335717/1000000000000 : ℝ) (501750233689/1000000000000 : ℝ) (501750233697/1000000000000 : ℝ) (501756284699/1000000000000 : ℝ) (501756284707/1000000000000 : ℝ) (250878142331/500000000000 : ℝ) (501756284671/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 4 (501756284699/1000000000000 : ℝ) (501756284707/1000000000000 : ℝ) (250878142331/500000000000 : ℝ) (501756284671/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 5 (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 6 (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8417/65536 : ℝ))) 7 (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8417/65536 : ℝ)) hmem 8 (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8417/65536 : ℝ))) hcmem 8 (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8417/65536 : ℝ)) (992021033953/1000000000000 : ℝ) (248005258489/250000000000 : ℝ) (12543907117/25000000000 : ℝ) (501756284689/1000000000000 : ℝ) (794496187019/1000000000000 : ℝ) (794496187037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1235_exp_lower
  have heNumeric : (2054900825989/1000000000000 : ℝ)/4 ≤ Real.exp (-42628273548493/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900825989/1000000000000 : ℝ)/4 ≤ Real.exp ((33667/262144 : ℝ)-(794496187037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33667/262144 : ℝ) (8417/65536 : ℝ) (794496187037/1000000000000 : ℝ) (2054900825989/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1236; no trusted numerical premise.
theorem cover8_leaf1236_exp_radius : (124749397943697671/125000000000000000 : ℝ) ≤ Real.exp ((-33669/2097152 : ℝ)/8) ∧ Real.exp ((-33669/2097152 : ℝ)/8) ≤ (997995183549581369/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33669/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1236_exp_lower : (920113409967809757/1000000000000000000 : ℝ) ≤ Real.exp ((-10657068138527/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657068138527/16000000000000 : ℝ)/8) ≤ (460056704983904879/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657068138527/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1236_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900857917/1000000000000 : ℝ) ≤ 4*Real.exp (8417/65536 : ℝ)*Real.exp (-mu (radius 8 (33669/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900857917/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33669/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1236_exp_radius
  have hrNumeric : (984073558373/1000000000000 : ℝ) ≤ Real.exp (-33669/2097152 : ℝ) ∧ Real.exp (-33669/2097152 : ℝ) ≤ (492036779187/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984073558373/1000000000000 : ℝ) ≤ (radius 8 (33669/262144 : ℝ)) ∧ (radius 8 (33669/262144 : ℝ)) ≤ (492036779187/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33669/262144 : ℝ)) (984073558373/1000000000000 : ℝ) (492036779187/500000000000 : ℝ) (88880863673/500000000000 : ℝ) (22220215919/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33669/262144 : ℝ)) (984073558373/1000000000000 : ℝ) (492036779187/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984073558373/1000000000000 : ℝ) (492036779187/500000000000 : ℝ) (496018389593/500000000000 : ℝ) (992036779187/1000000000000 : ℝ) (248001204429/250000000000 : ℝ) (496002408859/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 1 (496018389593/500000000000 : ℝ) (992036779187/1000000000000 : ℝ) (248001204429/250000000000 : ℝ) (496002408859/500000000000 : ℝ) (992020798451/1000000000000 : ℝ) (992020798453/1000000000000 : ℝ) (496010399161/500000000000 : ℝ) (248005199581/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 2 (992020798451/1000000000000 : ℝ) (992020798453/1000000000000 : ℝ) (496010399161/500000000000 : ℝ) (248005199581/250000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 3 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 4 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 5 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 6 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33669/262144 : ℝ)) 7 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33669/262144 : ℝ))) (88880863673/500000000000 : ℝ) (22220215919/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88880863673/500000000000 : ℝ) (22220215919/125000000000 : ℝ) (588880863673/1000000000000 : ℝ) (147220215919/250000000000 : ℝ) (84323597491/200000000000 : ℝ) (421617987463/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 1 (588880863673/1000000000000 : ℝ) (147220215919/250000000000 : ℝ) (84323597491/200000000000 : ℝ) (421617987463/1000000000000 : ℝ) (126312356391/250000000000 : ℝ) (50524942557/100000000000 : ℝ) (498279805523/1000000000000 : ℝ) (49827980553/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 2 (126312356391/250000000000 : ℝ) (50524942557/100000000000 : ℝ) (498279805523/1000000000000 : ℝ) (49827980553/100000000000 : ℝ) (501764615543/1000000000000 : ℝ) (10035292311/20000000000 : ℝ) (125438128551/250000000000 : ℝ) (125438128553/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 3 (501764615543/1000000000000 : ℝ) (10035292311/20000000000 : ℝ) (125438128551/250000000000 : ℝ) (125438128553/250000000000 : ℝ) (501758564873/1000000000000 : ℝ) (501758564881/1000000000000 : ℝ) (501758564837/1000000000000 : ℝ) (100351712969/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 4 (501758564873/1000000000000 : ℝ) (501758564881/1000000000000 : ℝ) (501758564837/1000000000000 : ℝ) (100351712969/200000000000 : ℝ) (100351712971/200000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 5 (100351712971/200000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 6 (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33669/262144 : ℝ))) 7 (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33669/262144 : ℝ)) hmem 8 (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33669/262144 : ℝ))) hcmem 8 (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33669/262144 : ℝ)) (496010399193/500000000000 : ℝ) (992020798389/1000000000000 : ℝ) (250879282427/500000000000 : ℝ) (501758564863/1000000000000 : ℝ) (39724999309/50000000000 : ℝ) (794499986197/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1236_exp_lower
  have heNumeric : (2054900857917/1000000000000 : ℝ)/4 ≤ Real.exp (-10657068138527/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900857917/1000000000000 : ℝ)/4 ≤ Real.exp ((8417/65536 : ℝ)-(794499986197/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8417/65536 : ℝ) (33669/262144 : ℝ) (794499986197/1000000000000 : ℝ) (2054900857917/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1237; no trusted numerical premise.
theorem cover8_leaf1237_exp_radius : (498997562032217369/500000000000000000 : ℝ) ≤ Real.exp ((-16835/1048576 : ℝ)/8) ∧ Real.exp ((-16835/1048576 : ℝ)/8) ≤ (997995124064434739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16835/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1237_exp_lower : (920113411763441629/1000000000000000000 : ℝ) ≤ Real.exp ((-42628271554923/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628271554923/64000000000000 : ℝ)/8) ≤ (92011341176344163/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628271554923/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1237_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900889999/1000000000000 : ℝ) ≤ 4*Real.exp (33669/262144 : ℝ)*Real.exp (-mu (radius 8 (16835/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900889999/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16835/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1237_exp_radius
  have hrNumeric : (98407308913/100000000000 : ℝ) ≤ Real.exp (-16835/1048576 : ℝ) ∧ Real.exp (-16835/1048576 : ℝ) ≤ (984073089131/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98407308913/100000000000 : ℝ) ≤ (radius 8 (16835/131072 : ℝ)) ∧ (radius 8 (16835/131072 : ℝ)) ≤ (984073089131/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16835/131072 : ℝ)) (98407308913/100000000000 : ℝ) (984073089131/1000000000000 : ℝ) (35552865003/200000000000 : ℝ) (177764325021/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16835/131072 : ℝ)) (98407308913/100000000000 : ℝ) (984073089131/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98407308913/100000000000 : ℝ) (984073089131/1000000000000 : ℝ) (198407308913/200000000000 : ℝ) (496018272283/500000000000 : ℝ) (248001145301/250000000000 : ℝ) (198400916241/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 1 (198407308913/200000000000 : ℝ) (496018272283/500000000000 : ℝ) (248001145301/250000000000 : ℝ) (198400916241/200000000000 : ℝ) (248005140721/250000000000 : ℝ) (496010281443/500000000000 : ℝ) (198404112551/200000000000 : ℝ) (992020562757/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 2 (248005140721/250000000000 : ℝ) (496010281443/500000000000 : ℝ) (198404112551/200000000000 : ℝ) (992020562757/1000000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 3 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 4 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 5 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 6 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16835/131072 : ℝ)) 7 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16835/131072 : ℝ))) (35552865003/200000000000 : ℝ) (177764325021/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35552865003/200000000000 : ℝ) (177764325021/1000000000000 : ℝ) (588882162507/1000000000000 : ℝ) (588882162511/1000000000000 : ℝ) (421621068039/1000000000000 : ℝ) (421621068047/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 1 (588882162507/1000000000000 : ℝ) (588882162511/1000000000000 : ℝ) (421621068039/1000000000000 : ℝ) (421621068047/1000000000000 : ℝ) (505251615273/1000000000000 : ℝ) (505251615279/1000000000000 : ℝ) (498282175383/1000000000000 : ℝ) (498282175391/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 2 (505251615273/1000000000000 : ℝ) (505251615279/1000000000000 : ℝ) (498282175383/1000000000000 : ℝ) (498282175391/1000000000000 : ℝ) (15680215479/31250000000 : ℝ) (100353379067/200000000000 : ℝ) (501754794669/1000000000000 : ℝ) (501754794677/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 3 (15680215479/31250000000 : ℝ) (100353379067/200000000000 : ℝ) (501754794669/1000000000000 : ℝ) (501754794677/1000000000000 : ℝ) (250880422499/500000000000 : ℝ) (250880422503/500000000000 : ℝ) (250880422481/500000000000 : ℝ) (50176084497/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 4 (250880422499/500000000000 : ℝ) (250880422503/500000000000 : ℝ) (250880422481/500000000000 : ℝ) (50176084497/100000000000 : ℝ) (25088042249/50000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 5 (25088042249/50000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 6 (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16835/131072 : ℝ))) 7 (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16835/131072 : ℝ)) hmem 8 (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16835/131072 : ℝ))) hcmem 8 (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16835/131072 : ℝ)) (992020562819/1000000000000 : ℝ) (496010281411/500000000000 : ℝ) (501760844979/1000000000000 : ℝ) (125440211247/250000000000 : ℝ) (49656486579/62500000000 : ℝ) (397251892641/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1237_exp_lower
  have heNumeric : (2054900889999/1000000000000 : ℝ)/4 ≤ Real.exp (-42628271554923/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900889999/1000000000000 : ℝ)/4 ≤ Real.exp ((33669/262144 : ℝ)-(397251892641/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33669/262144 : ℝ) (16835/131072 : ℝ) (397251892641/500000000000 : ℝ) (2054900889999/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1238; no trusted numerical premise.
theorem cover8_leaf1238_exp_radius : (498997532289645827/500000000000000000 : ℝ) ≤ Real.exp ((-33671/2097152 : ℝ)/8) ∧ Real.exp ((-33671/2097152 : ℝ)/8) ≤ (199599012915858331/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33671/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1238_exp_lower : (920113413567469539/1000000000000000000 : ℝ) ≤ Real.exp ((-21314135275533/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314135275533/32000000000000 : ℝ)/8) ≤ (46005670678373477/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314135275533/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1238_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490092223/100000000000 : ℝ) ≤ 4*Real.exp (16835/131072 : ℝ)*Real.exp (-mu (radius 8 (33671/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490092223/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33671/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1238_exp_radius
  have hrNumeric : (984072619887/1000000000000 : ℝ) ≤ Real.exp (-33671/2097152 : ℝ) ∧ Real.exp (-33671/2097152 : ℝ) ≤ (61504538743/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984072619887/1000000000000 : ℝ) ≤ (radius 8 (33671/262144 : ℝ)) ∧ (radius 8 (33671/262144 : ℝ)) ≤ (61504538743/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33671/262144 : ℝ)) (984072619887/1000000000000 : ℝ) (61504538743/62500000000 : ℝ) (35553384529/200000000000 : ℝ) (177766922651/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33671/262144 : ℝ)) (984072619887/1000000000000 : ℝ) (61504538743/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984072619887/1000000000000 : ℝ) (61504538743/62500000000 : ℝ) (992036309943/1000000000000 : ℝ) (124004538743/125000000000 : ℝ) (992004344691/1000000000000 : ℝ) (992004344693/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 1 (992036309943/1000000000000 : ℝ) (124004538743/125000000000 : ℝ) (992004344691/1000000000000 : ℝ) (992004344693/1000000000000 : ℝ) (992020327317/1000000000000 : ℝ) (992020327319/1000000000000 : ℝ) (248005081797/250000000000 : ℝ) (99202032719/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 2 (992020327317/1000000000000 : ℝ) (992020327319/1000000000000 : ℝ) (248005081797/250000000000 : ℝ) (99202032719/100000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 3 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 4 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 5 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 6 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33671/262144 : ℝ)) 7 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33671/262144 : ℝ))) (35553384529/200000000000 : ℝ) (177766922651/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35553384529/200000000000 : ℝ) (177766922651/1000000000000 : ℝ) (294441730661/500000000000 : ℝ) (294441730663/500000000000 : ℝ) (84324829711/200000000000 : ℝ) (421624148563/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 1 (294441730661/500000000000 : ℝ) (294441730663/500000000000 : ℝ) (84324829711/200000000000 : ℝ) (421624148563/1000000000000 : ℝ) (252626902469/500000000000 : ℝ) (101050760989/200000000000 : ℝ) (62285568149/125000000000 : ℝ) (1245711363/2500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 2 (252626902469/500000000000 : ℝ) (101050760989/200000000000 : ℝ) (62285568149/125000000000 : ℝ) (1245711363/2500000000 : ℝ) (100353835013/200000000000 : ℝ) (501769175073/1000000000000 : ℝ) (501757075087/1000000000000 : ℝ) (100351415019/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 3 (100353835013/200000000000 : ℝ) (501769175073/1000000000000 : ℝ) (501757075087/1000000000000 : ℝ) (100351415019/200000000000 : ℝ) (125440781269/250000000000 : ℝ) (125440781271/250000000000 : ℝ) (501763125039/1000000000000 : ℝ) (62720390631/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 4 (125440781269/250000000000 : ℝ) (125440781271/250000000000 : ℝ) (501763125039/1000000000000 : ℝ) (62720390631/125000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 5 (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 6 (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33671/262144 : ℝ))) 7 (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33671/262144 : ℝ)) hmem 8 (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33671/262144 : ℝ))) hcmem 8 (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33671/262144 : ℝ)) (248005081813/250000000000 : ℝ) (198404065451/200000000000 : ℝ) (501763125057/1000000000000 : ℝ) (250881562533/500000000000 : ℝ) (198626896069/250000000000 : ℝ) (397253792147/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1238_exp_lower
  have heNumeric : (205490092223/100000000000 : ℝ)/4 ≤ Real.exp (-21314135275533/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490092223/100000000000 : ℝ)/4 ≤ Real.exp ((16835/131072 : ℝ)-(397253792147/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16835/131072 : ℝ) (33671/262144 : ℝ) (397253792147/500000000000 : ℝ) (205490092223/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1239; no trusted numerical premise.
theorem cover8_leaf1239_exp_radius : (498997502547076057/500000000000000000 : ℝ) ≤ Real.exp ((-4209/262144 : ℝ)/8) ∧ Real.exp ((-4209/262144 : ℝ)/8) ≤ (199599001018830423/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4209/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1239_exp_lower : (230028353845289661/250000000000000000 : ℝ) ≤ Real.exp ((-42628269541833/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628269541833/64000000000000 : ℝ)/8) ≤ (184022683076231729/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628269541833/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1239_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450477317/500000000000 : ℝ) ≤ 4*Real.exp (33671/262144 : ℝ)*Real.exp (-mu (radius 8 (4209/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450477317/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4209/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1239_exp_radius
  have hrNumeric : (196814430129/200000000000 : ℝ) ≤ Real.exp (-4209/262144 : ℝ) ∧ Real.exp (-4209/262144 : ℝ) ≤ (492036075323/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196814430129/200000000000 : ℝ) ≤ (radius 8 (4209/32768 : ℝ)) ∧ (radius 8 (4209/32768 : ℝ)) ≤ (492036075323/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4209/32768 : ℝ)) (196814430129/200000000000 : ℝ) (492036075323/500000000000 : ℝ) (17776952023/100000000000 : ℝ) (44442380059/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4209/32768 : ℝ)) (196814430129/200000000000 : ℝ) (492036075323/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196814430129/200000000000 : ℝ) (492036075323/500000000000 : ℝ) (496018037661/500000000000 : ℝ) (992036075323/1000000000000 : ℝ) (992004108179/1000000000000 : ℝ) (992004108181/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 1 (496018037661/500000000000 : ℝ) (992036075323/1000000000000 : ℝ) (992004108179/1000000000000 : ℝ) (992004108181/1000000000000 : ℝ) (3968080367/4000000000 : ℝ) (124002511469/125000000000 : ℝ) (992020091621/1000000000000 : ℝ) (124002511453/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 2 (3968080367/4000000000 : ℝ) (124002511469/125000000000 : ℝ) (992020091621/1000000000000 : ℝ) (124002511453/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 3 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 4 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 5 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 6 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4209/32768 : ℝ)) 7 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4209/32768 : ℝ))) (17776952023/100000000000 : ℝ) (44442380059/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17776952023/100000000000 : ℝ) (44442380059/250000000000 : ℝ) (117776952023/200000000000 : ℝ) (294442380059/500000000000 : ℝ) (210813614497/500000000000 : ℝ) (421627229003/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 1 (117776952023/200000000000 : ℝ) (294442380059/500000000000 : ℝ) (210813614497/500000000000 : ℝ) (421627229003/1000000000000 : ℝ) (252627997277/500000000000 : ℝ) (505255994561/1000000000000 : ℝ) (498286914943/1000000000000 : ℝ) (498286914951/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 2 (252627997277/500000000000 : ℝ) (505255994561/1000000000000 : ℝ) (498286914943/1000000000000 : ℝ) (498286914951/1000000000000 : ℝ) (125442863687/250000000000 : ℝ) (125442863689/250000000000 : ℝ) (501759355451/1000000000000 : ℝ) (501759355459/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 3 (125442863687/250000000000 : ℝ) (125442863689/250000000000 : ℝ) (501759355451/1000000000000 : ℝ) (501759355459/1000000000000 : ℝ) (501765405099/1000000000000 : ℝ) (125441351277/250000000000 : ℝ) (501765405063/1000000000000 : ℝ) (31360337817/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 4 (501765405099/1000000000000 : ℝ) (125441351277/250000000000 : ℝ) (501765405063/1000000000000 : ℝ) (31360337817/62500000000 : ℝ) (501765405081/1000000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 5 (501765405081/1000000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 6 (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4209/32768 : ℝ))) 7 (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4209/32768 : ℝ)) hmem 8 (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4209/32768 : ℝ))) hcmem 8 (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4209/32768 : ℝ)) (198404018337/200000000000 : ℝ) (124002511461/125000000000 : ℝ) (12544135127/25000000000 : ℝ) (50176540509/100000000000 : ℝ) (794511383203/1000000000000 : ℝ) (397255691611/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1239_exp_lower
  have heNumeric : (1027450477317/500000000000 : ℝ)/4 ≤ Real.exp (-42628269541833/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450477317/500000000000 : ℝ)/4 ≤ Real.exp ((33671/262144 : ℝ)-(397255691611/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33671/262144 : ℝ) (4209/32768 : ℝ) (397255691611/500000000000 : ℝ) (1027450477317/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1240; no trusted numerical premise.
theorem cover8_leaf1240_exp_radius : (997994945609016121/1000000000000000000 : ℝ) ≤ Real.exp ((-33673/2097152 : ℝ)/8) ∧ Real.exp ((-33673/2097152 : ℝ)/8) ≤ (498997472804508061/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33673/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1240_exp_lower : (115014177150434227/125000000000000000 : ℝ) ≤ Real.exp ((-213141342639/320000000000 : ℝ)/8) ∧ Real.exp ((-213141342639/320000000000 : ℝ)/8) ≤ (920113417203473817/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213141342639/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1240_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900987193/1000000000000 : ℝ) ≤ 4*Real.exp (4209/32768 : ℝ)*Real.exp (-mu (radius 8 (33673/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900987193/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33673/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1240_exp_radius
  have hrNumeric : (984071681403/1000000000000 : ℝ) ≤ Real.exp (-33673/2097152 : ℝ) ∧ Real.exp (-33673/2097152 : ℝ) ≤ (246017920351/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984071681403/1000000000000 : ℝ) ≤ (radius 8 (33673/262144 : ℝ)) ∧ (radius 8 (33673/262144 : ℝ)) ≤ (246017920351/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33673/262144 : ℝ)) (984071681403/1000000000000 : ℝ) (246017920351/250000000000 : ℝ) (11110757361/62500000000 : ℝ) (88886058891/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33673/262144 : ℝ)) (984071681403/1000000000000 : ℝ) (246017920351/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984071681403/1000000000000 : ℝ) (246017920351/250000000000 : ℝ) (992035840701/1000000000000 : ℝ) (496017920351/500000000000 : ℝ) (992003871667/1000000000000 : ℝ) (248000967917/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 1 (992035840701/1000000000000 : ℝ) (496017920351/500000000000 : ℝ) (992003871667/1000000000000 : ℝ) (248000967917/250000000000 : ℝ) (124002482023/125000000000 : ℝ) (198403971237/200000000000 : ℝ) (198403971211/200000000000 : ℝ) (992019856057/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 2 (124002482023/125000000000 : ℝ) (198403971237/200000000000 : ℝ) (198403971211/200000000000 : ℝ) (992019856057/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 3 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 4 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 5 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 6 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33673/262144 : ℝ)) 7 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33673/262144 : ℝ))) (11110757361/62500000000 : ℝ) (88886058891/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11110757361/62500000000 : ℝ) (88886058891/500000000000 : ℝ) (73610757361/125000000000 : ℝ) (588886058891/1000000000000 : ℝ) (84326061873/200000000000 : ℝ) (210815154687/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 1 (73610757361/125000000000 : ℝ) (588886058891/1000000000000 : ℝ) (84326061873/200000000000 : ℝ) (210815154687/500000000000 : ℝ) (252629092063/500000000000 : ℝ) (505258184133/1000000000000 : ℝ) (249144642321/500000000000 : ℝ) (9965785693/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 2 (252629092063/500000000000 : ℝ) (505258184133/1000000000000 : ℝ) (249144642321/500000000000 : ℝ) (9965785693/20000000000 : ℝ) (31360858399/62500000000 : ℝ) (62721716799/125000000000 : ℝ) (501761635767/1000000000000 : ℝ) (20070465431/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 3 (31360858399/62500000000 : ℝ) (62721716799/125000000000 : ℝ) (501761635767/1000000000000 : ℝ) (20070465431/40000000000 : ℝ) (20070707403/40000000000 : ℝ) (125441921271/250000000000 : ℝ) (501767685039/1000000000000 : ℝ) (62720960631/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 4 (20070707403/40000000000 : ℝ) (125441921271/250000000000 : ℝ) (501767685039/1000000000000 : ℝ) (62720960631/125000000000 : ℝ) (501767685057/1000000000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 5 (501767685057/1000000000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 6 (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33673/262144 : ℝ))) 7 (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33673/262144 : ℝ)) hmem 8 (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33673/262144 : ℝ))) hcmem 8 (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33673/262144 : ℝ)) (992019856119/1000000000000 : ℝ) (992019856121/1000000000000 : ℝ) (7840120079/15625000000 : ℝ) (250883842533/500000000000 : ℝ) (794515182057/1000000000000 : ℝ) (31780607283/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1240_exp_lower
  have heNumeric : (2054900987193/1000000000000 : ℝ)/4 ≤ Real.exp (-213141342639/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900987193/1000000000000 : ℝ)/4 ≤ Real.exp ((4209/32768 : ℝ)-(31780607283/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4209/32768 : ℝ) (33673/262144 : ℝ) (31780607283/40000000000 : ℝ) (2054900987193/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1241; no trusted numerical premise.
theorem cover8_leaf1241_exp_radius : (997994886123883673/1000000000000000000 : ℝ) ≤ Real.exp ((-16837/1048576 : ℝ)/8) ∧ Real.exp ((-16837/1048576 : ℝ)/8) ≤ (498997443061941837/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16837/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1241_exp_lower : (460056709517207527/500000000000000000 : ℝ) ≤ Real.exp ((-42628267508967/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628267508967/64000000000000 : ℝ)/8) ≤ (184022683806883011/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628267508967/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1241_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980203981/200000000000 : ℝ) ≤ 4*Real.exp (33673/262144 : ℝ)*Real.exp (-mu (radius 8 (16837/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980203981/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16837/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1241_exp_radius
  have hrNumeric : (984071212161/1000000000000 : ℝ) ≤ Real.exp (-16837/1048576 : ℝ) ∧ Real.exp (-16837/1048576 : ℝ) ≤ (492035606081/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984071212161/1000000000000 : ℝ) ≤ (radius 8 (16837/131072 : ℝ)) ∧ (radius 8 (16837/131072 : ℝ)) ≤ (492035606081/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16837/131072 : ℝ)) (984071212161/1000000000000 : ℝ) (492035606081/500000000000 : ℝ) (177774715283/1000000000000 : ℝ) (177774715289/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16837/131072 : ℝ)) (984071212161/1000000000000 : ℝ) (492035606081/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984071212161/1000000000000 : ℝ) (492035606081/500000000000 : ℝ) (3100111269/3125000000 : ℝ) (992035606081/1000000000000 : ℝ) (198400727031/200000000000 : ℝ) (248000908789/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 1 (3100111269/3125000000 : ℝ) (992035606081/1000000000000 : ℝ) (198400727031/200000000000 : ℝ) (248000908789/250000000000 : ℝ) (992019620617/1000000000000 : ℝ) (992019620619/1000000000000 : ℝ) (124002452561/125000000000 : ℝ) (99201962049/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 2 (992019620617/1000000000000 : ℝ) (992019620619/1000000000000 : ℝ) (124002452561/125000000000 : ℝ) (99201962049/100000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 3 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 4 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 5 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 6 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16837/131072 : ℝ)) 7 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16837/131072 : ℝ))) (177774715283/1000000000000 : ℝ) (177774715289/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177774715283/1000000000000 : ℝ) (177774715289/1000000000000 : ℝ) (588887357641/1000000000000 : ℝ) (117777471529/200000000000 : ℝ) (105408347417/250000000000 : ℝ) (105408347419/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 1 (588887357641/1000000000000 : ℝ) (117777471529/200000000000 : ℝ) (105408347417/250000000000 : ℝ) (105408347419/250000000000 : ℝ) (252630186827/500000000000 : ℝ) (505260373661/1000000000000 : ℝ) (498291654289/1000000000000 : ℝ) (498291654297/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 2 (252630186827/500000000000 : ℝ) (505260373661/1000000000000 : ℝ) (498291654289/1000000000000 : ℝ) (498291654297/1000000000000 : ℝ) (501776013971/1000000000000 : ℝ) (501776013979/1000000000000 : ℝ) (250881958017/500000000000 : ℝ) (501763916043/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 3 (501776013971/1000000000000 : ℝ) (501776013979/1000000000000 : ℝ) (250881958017/500000000000 : ℝ) (501763916043/1000000000000 : ℝ) (250884982501/500000000000 : ℝ) (501769965011/1000000000000 : ℝ) (250884982483/500000000000 : ℝ) (20070798599/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 4 (250884982501/500000000000 : ℝ) (501769965011/1000000000000 : ℝ) (250884982483/500000000000 : ℝ) (20070798599/40000000000 : ℝ) (62721245623/125000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 5 (62721245623/125000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 6 (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16837/131072 : ℝ))) 7 (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16837/131072 : ℝ)) hmem 8 (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16837/131072 : ℝ))) hcmem 8 (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16837/131072 : ℝ)) (124002452569/125000000000 : ℝ) (198403924111/200000000000 : ℝ) (501769964983/1000000000000 : ℝ) (501769964993/1000000000000 : ℝ) (397259490417/500000000000 : ℝ) (794518980853/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1241_exp_lower
  have heNumeric : (410980203981/200000000000 : ℝ)/4 ≤ Real.exp (-42628267508967/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980203981/200000000000 : ℝ)/4 ≤ Real.exp ((33673/262144 : ℝ)-(794518980853/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33673/262144 : ℝ) (16837/131072 : ℝ) (794518980853/1000000000000 : ℝ) (410980203981/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1242; no trusted numerical premise.
theorem cover8_leaf1242_exp_radius : (997994826638754771/1000000000000000000 : ℝ) ≤ Real.exp ((-33675/2097152 : ℝ)/8) ∧ Real.exp ((-33675/2097152 : ℝ)/8) ≤ (249498706659688693/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33675/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1242_exp_lower : (920113420874787459/1000000000000000000 : ℝ) ≤ Real.exp ((-21314133242443/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314133242443/32000000000000 : ℝ)/8) ≤ (46005671043739373/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314133242443/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1242_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450526393/500000000000 : ℝ) ≤ 4*Real.exp (16837/131072 : ℝ)*Real.exp (-mu (radius 8 (33675/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450526393/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33675/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1242_exp_radius
  have hrNumeric : (24601768573/25000000000 : ℝ) ≤ Real.exp (-33675/2097152 : ℝ) ∧ Real.exp (-33675/2097152 : ℝ) ≤ (984070742921/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24601768573/25000000000 : ℝ) ≤ (radius 8 (33675/262144 : ℝ)) ∧ (radius 8 (33675/262144 : ℝ)) ≤ (984070742921/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33675/262144 : ℝ)) (24601768573/25000000000 : ℝ) (984070742921/1000000000000 : ℝ) (35555462549/200000000000 : ℝ) (177777312751/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33675/262144 : ℝ)) (24601768573/25000000000 : ℝ) (984070742921/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24601768573/25000000000 : ℝ) (984070742921/1000000000000 : ℝ) (49601768573/50000000000 : ℝ) (992035371461/1000000000000 : ℝ) (992003398643/1000000000000 : ℝ) (248000849661/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 1 (49601768573/50000000000 : ℝ) (992035371461/1000000000000 : ℝ) (992003398643/1000000000000 : ℝ) (248000849661/250000000000 : ℝ) (992019385051/1000000000000 : ℝ) (992019385053/1000000000000 : ℝ) (496009692461/500000000000 : ℝ) (248004846231/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 2 (992019385051/1000000000000 : ℝ) (992019385053/1000000000000 : ℝ) (496009692461/500000000000 : ℝ) (248004846231/250000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 3 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 4 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 5 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 6 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33675/262144 : ℝ)) 7 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33675/262144 : ℝ))) (35555462549/200000000000 : ℝ) (177777312751/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35555462549/200000000000 : ℝ) (177777312751/1000000000000 : ℝ) (147222164093/250000000000 : ℝ) (73611082047/125000000000 : ℝ) (210818234947/500000000000 : ℝ) (210818234951/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 1 (147222164093/250000000000 : ℝ) (73611082047/125000000000 : ℝ) (210818234947/500000000000 : ℝ) (210818234951/500000000000 : ℝ) (505262563133/1000000000000 : ℝ) (505262563139/1000000000000 : ℝ) (249147011939/500000000000 : ℝ) (249147011943/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 2 (505262563133/1000000000000 : ℝ) (505262563139/1000000000000 : ℝ) (249147011939/500000000000 : ℝ) (249147011943/500000000000 : ℝ) (100355658701/200000000000 : ℝ) (501778293513/1000000000000 : ℝ) (501766196249/1000000000000 : ℝ) (501766196257/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 3 (100355658701/200000000000 : ℝ) (501778293513/1000000000000 : ℝ) (501766196249/1000000000000 : ℝ) (501766196257/1000000000000 : ℝ) (501772244877/1000000000000 : ℝ) (100354448977/200000000000 : ℝ) (12544306121/25000000000 : ℝ) (501772244849/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 4 (501772244877/1000000000000 : ℝ) (100354448977/200000000000 : ℝ) (12544306121/25000000000 : ℝ) (501772244849/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 5 (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 6 (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33675/262144 : ℝ))) 7 (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33675/262144 : ℝ)) hmem 8 (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33675/262144 : ℝ))) hcmem 8 (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33675/262144 : ℝ)) (496009692493/500000000000 : ℝ) (992019384989/1000000000000 : ℝ) (250886122429/500000000000 : ℝ) (501772244867/1000000000000 : ℝ) (794522779531/1000000000000 : ℝ) (794522779549/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1242_exp_lower
  have heNumeric : (1027450526393/500000000000 : ℝ)/4 ≤ Real.exp (-21314133242443/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450526393/500000000000 : ℝ)/4 ≤ Real.exp ((16837/131072 : ℝ)-(794522779549/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16837/131072 : ℝ) (33675/262144 : ℝ) (794522779549/1000000000000 : ℝ) (1027450526393/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1243; no trusted numerical premise.
theorem cover8_leaf1243_exp_radius : (498997383576814707/500000000000000000 : ℝ) ≤ Real.exp ((-8419/524288 : ℝ)/8) ∧ Real.exp ((-8419/524288 : ℝ)/8) ≤ (199598953430725883/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8419/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1243_exp_lower : (920113422722865817/1000000000000000000 : ℝ) ≤ Real.exp ((-42628265456517/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628265456517/64000000000000 : ℝ)/8) ≤ (460056711361432909/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628265456517/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1243_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980217161/200000000000 : ℝ) ≤ 4*Real.exp (33675/262144 : ℝ)*Real.exp (-mu (radius 8 (8419/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980217161/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8419/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1243_exp_radius
  have hrNumeric : (492035136839/500000000000 : ℝ) ≤ Real.exp (-8419/524288 : ℝ) ∧ Real.exp (-8419/524288 : ℝ) ≤ (984070273679/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492035136839/500000000000 : ℝ) ≤ (radius 8 (8419/65536 : ℝ)) ∧ (radius 8 (8419/65536 : ℝ)) ≤ (984070273679/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8419/65536 : ℝ)) (492035136839/500000000000 : ℝ) (984070273679/1000000000000 : ℝ) (177779910173/1000000000000 : ℝ) (8888995509/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8419/65536 : ℝ)) (492035136839/500000000000 : ℝ) (984070273679/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492035136839/500000000000 : ℝ) (984070273679/1000000000000 : ℝ) (992035136839/1000000000000 : ℝ) (24800878421/25000000000 : ℝ) (992003162131/1000000000000 : ℝ) (248000790533/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 1 (992035136839/1000000000000 : ℝ) (24800878421/25000000000 : ℝ) (992003162131/1000000000000 : ℝ) (248000790533/250000000000 : ℝ) (198403829897/200000000000 : ℝ) (496009574743/500000000000 : ℝ) (248004787339/250000000000 : ℝ) (496009574679/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 2 (198403829897/200000000000 : ℝ) (496009574743/500000000000 : ℝ) (248004787339/250000000000 : ℝ) (496009574679/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 3 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 4 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 5 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 6 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8419/65536 : ℝ)) 7 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8419/65536 : ℝ))) (177779910173/1000000000000 : ℝ) (8888995509/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177779910173/1000000000000 : ℝ) (8888995509/50000000000 : ℝ) (294444977543/500000000000 : ℝ) (58888995509/100000000000 : ℝ) (421639550057/1000000000000 : ℝ) (421639550067/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 1 (294444977543/500000000000 : ℝ) (58888995509/100000000000 : ℝ) (421639550057/1000000000000 : ℝ) (421639550067/1000000000000 : ℝ) (505264752571/1000000000000 : ℝ) (505264752579/1000000000000 : ℝ) (24914819671/50000000000 : ℝ) (124574098357/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 2 (505264752571/1000000000000 : ℝ) (505264752579/1000000000000 : ℝ) (24914819671/50000000000 : ℝ) (124574098357/250000000000 : ℝ) (100356114599/200000000000 : ℝ) (125445143251/250000000000 : ℝ) (501768476419/1000000000000 : ℝ) (125442119107/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 3 (100356114599/200000000000 : ℝ) (125445143251/250000000000 : ℝ) (501768476419/1000000000000 : ℝ) (125442119107/250000000000 : ℝ) (501774524707/1000000000000 : ℝ) (125443631179/250000000000 : ℝ) (50177452467/100000000000 : ℝ) (12544363117/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 4 (501774524707/1000000000000 : ℝ) (125443631179/250000000000 : ℝ) (50177452467/100000000000 : ℝ) (12544363117/25000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 5 (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 6 (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8419/65536 : ℝ))) 7 (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8419/65536 : ℝ)) hmem 8 (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8419/65536 : ℝ))) hcmem 8 (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8419/65536 : ℝ)) (49600957471/50000000000 : ℝ) (496009574711/500000000000 : ℝ) (31360907793/62500000000 : ℝ) (250887262349/500000000000 : ℝ) (794526578159/1000000000000 : ℝ) (397263289089/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1243_exp_lower
  have heNumeric : (410980217161/200000000000 : ℝ)/4 ≤ Real.exp (-42628265456517/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980217161/200000000000 : ℝ)/4 ≤ Real.exp ((33675/262144 : ℝ)-(397263289089/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33675/262144 : ℝ) (8419/65536 : ℝ) (397263289089/500000000000 : ℝ) (410980217161/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1244; no trusted numerical premise.
theorem cover8_leaf1244_exp_radius : (997994707668507603/1000000000000000000 : ℝ) ≤ Real.exp ((-33677/2097152 : ℝ)/8) ∧ Real.exp ((-33677/2097152 : ℝ)/8) ≤ (249498676917126901/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33677/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1244_exp_lower : (230028356145122589/250000000000000000 : ℝ) ≤ Real.exp ((-10657066105709/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657066105709/16000000000000 : ℝ)/8) ≤ (920113424580490357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657066105709/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1244_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450559497/500000000000 : ℝ) ≤ 4*Real.exp (8419/65536 : ℝ)*Real.exp (-mu (radius 8 (33677/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450559497/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33677/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1244_exp_radius
  have hrNumeric : (984069804437/1000000000000 : ℝ) ≤ Real.exp (-33677/2097152 : ℝ) ∧ Real.exp (-33677/2097152 : ℝ) ≤ (492034902219/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984069804437/1000000000000 : ℝ) ≤ (radius 8 (33677/262144 : ℝ)) ∧ (radius 8 (33677/262144 : ℝ)) ≤ (492034902219/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33677/262144 : ℝ)) (984069804437/1000000000000 : ℝ) (492034902219/500000000000 : ℝ) (177782507557/1000000000000 : ℝ) (177782507563/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33677/262144 : ℝ)) (984069804437/1000000000000 : ℝ) (492034902219/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984069804437/1000000000000 : ℝ) (492034902219/500000000000 : ℝ) (496017451109/500000000000 : ℝ) (992034902219/1000000000000 : ℝ) (992002925619/1000000000000 : ℝ) (49600146281/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 1 (496017451109/500000000000 : ℝ) (992034902219/1000000000000 : ℝ) (992002925619/1000000000000 : ℝ) (49600146281/50000000000 : ℝ) (496009456959/500000000000 : ℝ) (1550029553/1562500000 : ℝ) (992018913789/1000000000000 : ℝ) (992018913791/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 2 (496009456959/500000000000 : ℝ) (1550029553/1562500000 : ℝ) (992018913789/1000000000000 : ℝ) (992018913791/1000000000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 3 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 4 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 5 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 6 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33677/262144 : ℝ)) 7 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33677/262144 : ℝ))) (177782507557/1000000000000 : ℝ) (177782507563/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177782507557/1000000000000 : ℝ) (177782507563/1000000000000 : ℝ) (294445626889/500000000000 : ℝ) (294445626891/500000000000 : ℝ) (210821315073/500000000000 : ℝ) (210821315077/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 1 (294445626889/500000000000 : ℝ) (294445626891/500000000000 : ℝ) (210821315073/500000000000 : ℝ) (210821315077/500000000000 : ℝ) (252633470981/500000000000 : ℝ) (31579183873/62500000000 : ℝ) (99659752581/200000000000 : ℝ) (15571836341/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 2 (252633470981/500000000000 : ℝ) (31579183873/62500000000 : ℝ) (99659752581/200000000000 : ℝ) (15571836341/31250000000 : ℝ) (501782852433/1000000000000 : ℝ) (12544571311/25000000000 : ℝ) (501770756537/1000000000000 : ℝ) (100354151309/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 3 (501782852433/1000000000000 : ℝ) (12544571311/25000000000 : ℝ) (501770756537/1000000000000 : ℝ) (100354151309/200000000000 : ℝ) (100355360897/200000000000 : ℝ) (501776804493/1000000000000 : ℝ) (15680525139/31250000000 : ℝ) (501776804457/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 4 (100355360897/200000000000 : ℝ) (501776804493/1000000000000 : ℝ) (15680525139/31250000000 : ℝ) (501776804457/1000000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 5 (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 6 (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33677/262144 : ℝ))) 7 (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33677/262144 : ℝ)) hmem 8 (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33677/262144 : ℝ))) hcmem 8 (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33677/262144 : ℝ)) (992018913853/1000000000000 : ℝ) (15500295529/15625000000 : ℝ) (250888402233/500000000000 : ℝ) (20071072179/40000000000 : ℝ) (397265188353/500000000000 : ℝ) (198632594181/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1244_exp_lower
  have heNumeric : (1027450559497/500000000000 : ℝ)/4 ≤ Real.exp (-10657066105709/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450559497/500000000000 : ℝ)/4 ≤ Real.exp ((8419/65536 : ℝ)-(198632594181/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8419/65536 : ℝ) (33677/262144 : ℝ) (198632594181/250000000000 : ℝ) (1027450559497/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1245; no trusted numerical premise.
theorem cover8_leaf1245_exp_radius : (498997324091694669/500000000000000000 : ℝ) ≤ Real.exp ((-16839/1048576 : ℝ)/8) ∧ Real.exp ((-16839/1048576 : ℝ)/8) ≤ (997994648183389339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16839/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1245_exp_lower : (460056713223370481/500000000000000000 : ℝ) ≤ Real.exp ((-8525652676871/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525652676871/12800000000000 : ℝ)/8) ≤ (920113426446740963/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525652676871/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1245_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450576169/500000000000 : ℝ) ≤ 4*Real.exp (33677/262144 : ℝ)*Real.exp (-mu (radius 8 (16839/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450576169/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16839/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1245_exp_radius
  have hrNumeric : (246017333799/250000000000 : ℝ) ≤ Real.exp (-16839/1048576 : ℝ) ∧ Real.exp (-16839/1048576 : ℝ) ≤ (984069335197/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246017333799/250000000000 : ℝ) ≤ (radius 8 (16839/131072 : ℝ)) ∧ (radius 8 (16839/131072 : ℝ)) ≤ (984069335197/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16839/131072 : ℝ)) (246017333799/250000000000 : ℝ) (984069335197/1000000000000 : ℝ) (177785104901/1000000000000 : ℝ) (44446276227/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16839/131072 : ℝ)) (246017333799/250000000000 : ℝ) (984069335197/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246017333799/250000000000 : ℝ) (984069335197/1000000000000 : ℝ) (496017333799/500000000000 : ℝ) (992034667599/1000000000000 : ℝ) (992002689107/1000000000000 : ℝ) (248000672277/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 1 (496017333799/500000000000 : ℝ) (992034667599/1000000000000 : ℝ) (992002689107/1000000000000 : ℝ) (248000672277/250000000000 : ℝ) (62001167397/62500000000 : ℝ) (496009339177/500000000000 : ℝ) (992018678223/1000000000000 : ℝ) (39680747129/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 2 (62001167397/62500000000 : ℝ) (496009339177/500000000000 : ℝ) (992018678223/1000000000000 : ℝ) (39680747129/40000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 3 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 4 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 5 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 6 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16839/131072 : ℝ)) 7 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16839/131072 : ℝ))) (177785104901/1000000000000 : ℝ) (44446276227/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177785104901/1000000000000 : ℝ) (44446276227/250000000000 : ℝ) (11777851049/20000000000 : ℝ) (294446276227/500000000000 : ℝ) (84329142033/200000000000 : ℝ) (210822855087/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 1 (11777851049/20000000000 : ℝ) (294446276227/500000000000 : ℝ) (84329142033/200000000000 : ℝ) (210822855087/500000000000 : ℝ) (505269131307/1000000000000 : ℝ) (252634565657/500000000000 : ℝ) (498301132337/1000000000000 : ℝ) (99660226469/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 2 (505269131307/1000000000000 : ℝ) (252634565657/500000000000 : ℝ) (498301132337/1000000000000 : ℝ) (99660226469/200000000000 : ℝ) (250892565911/500000000000 : ℝ) (50178513183/100000000000 : ℝ) (250886518303/500000000000 : ℝ) (250886518307/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 3 (250892565911/500000000000 : ℝ) (50178513183/100000000000 : ℝ) (250886518303/500000000000 : ℝ) (250886518307/500000000000 : ℝ) (250889542107/500000000000 : ℝ) (250889542111/500000000000 : ℝ) (501779084177/1000000000000 : ℝ) (250889542093/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 4 (250889542107/500000000000 : ℝ) (250889542111/500000000000 : ℝ) (501779084177/1000000000000 : ℝ) (250889542093/500000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 5 (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 6 (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16839/131072 : ℝ))) 7 (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16839/131072 : ℝ)) hmem 8 (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16839/131072 : ℝ))) hcmem 8 (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16839/131072 : ℝ)) (992018678287/1000000000000 : ℝ) (99201867829/100000000000 : ℝ) (100355816839/200000000000 : ℝ) (125444771051/250000000000 : ℝ) (794534175177/1000000000000 : ℝ) (158906835039/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1245_exp_lower
  have heNumeric : (1027450576169/500000000000 : ℝ)/4 ≤ Real.exp (-8525652676871/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450576169/500000000000 : ℝ)/4 ≤ Real.exp ((33677/262144 : ℝ)-(158906835039/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33677/262144 : ℝ) (16839/131072 : ℝ) (158906835039/200000000000 : ℝ) (1027450576169/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1246; no trusted numerical premise.
theorem cover8_leaf1246_exp_radius : (498997294349137309/500000000000000000 : ℝ) ≤ Real.exp ((-33679/2097152 : ℝ)/8) ∧ Real.exp ((-33679/2097152 : ℝ)/8) ≤ (997994588698274619/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33679/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1246_exp_lower : (230028357080519423/250000000000000000 : ℝ) ≤ Real.exp ((-21314131170409/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314131170409/32000000000000 : ℝ)/8) ≤ (920113428322077693/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314131170409/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1246_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901185843/1000000000000 : ℝ) ≤ 4*Real.exp (16839/131072 : ℝ)*Real.exp (-mu (radius 8 (33679/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901185843/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33679/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1246_exp_radius
  have hrNumeric : (246017216489/250000000000 : ℝ) ≤ Real.exp (-33679/2097152 : ℝ) ∧ Real.exp (-33679/2097152 : ℝ) ≤ (984068865957/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246017216489/250000000000 : ℝ) ≤ (radius 8 (33679/262144 : ℝ)) ∧ (radius 8 (33679/262144 : ℝ)) ≤ (984068865957/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33679/262144 : ℝ)) (246017216489/250000000000 : ℝ) (984068865957/1000000000000 : ℝ) (177787702201/1000000000000 : ℝ) (2777932847/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33679/262144 : ℝ)) (246017216489/250000000000 : ℝ) (984068865957/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246017216489/250000000000 : ℝ) (984068865957/1000000000000 : ℝ) (496017216489/500000000000 : ℝ) (992034432979/1000000000000 : ℝ) (198400490519/200000000000 : ℝ) (992002452597/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 1 (496017216489/500000000000 : ℝ) (992034432979/1000000000000 : ℝ) (198400490519/200000000000 : ℝ) (992002452597/1000000000000 : ℝ) (496009221393/500000000000 : ℝ) (248004610697/250000000000 : ℝ) (992018442657/1000000000000 : ℝ) (49600922133/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 2 (496009221393/500000000000 : ℝ) (248004610697/250000000000 : ℝ) (992018442657/1000000000000 : ℝ) (49600922133/50000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 3 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 4 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 5 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 6 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33679/262144 : ℝ)) 7 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33679/262144 : ℝ))) (177787702201/1000000000000 : ℝ) (2777932847/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177787702201/1000000000000 : ℝ) (2777932847/15625000000 : ℝ) (5888938511/10000000000 : ℝ) (18402932847/31250000000 : ℝ) (421648790109/1000000000000 : ℝ) (421648790119/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 1 (5888938511/10000000000 : ℝ) (18402932847/31250000000 : ℝ) (421648790109/1000000000000 : ℝ) (421648790119/1000000000000 : ℝ) (126317830151/250000000000 : ℝ) (126317830153/250000000000 : ℝ) (31143968857/62500000000 : ℝ) (498303501721/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 2 (126317830151/250000000000 : ℝ) (126317830153/250000000000 : ℝ) (31143968857/62500000000 : ℝ) (498303501721/1000000000000 : ℝ) (250893705579/500000000000 : ℝ) (501787411167/1000000000000 : ℝ) (250887658311/500000000000 : ℝ) (62721914579/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 3 (250893705579/500000000000 : ℝ) (501787411167/1000000000000 : ℝ) (250887658311/500000000000 : ℝ) (62721914579/125000000000 : ℝ) (50178136389/100000000000 : ℝ) (5017813639/10000000000 : ℝ) (501781363853/1000000000000 : ℝ) (62722670483/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 4 (50178136389/100000000000 : ℝ) (5017813639/10000000000 : ℝ) (501781363853/1000000000000 : ℝ) (62722670483/125000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 5 (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 6 (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33679/262144 : ℝ))) 7 (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33679/262144 : ℝ)) hmem 8 (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33679/262144 : ℝ))) hcmem 8 (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33679/262144 : ℝ)) (992018442721/1000000000000 : ℝ) (248004610681/250000000000 : ℝ) (501781363871/1000000000000 : ℝ) (250890681941/500000000000 : ℝ) (397268986783/500000000000 : ℝ) (794537973587/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1246_exp_lower
  have heNumeric : (2054901185843/1000000000000 : ℝ)/4 ≤ Real.exp (-21314131170409/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901185843/1000000000000 : ℝ)/4 ≤ Real.exp ((16839/131072 : ℝ)-(794537973587/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16839/131072 : ℝ) (33679/262144 : ℝ) (794537973587/1000000000000 : ℝ) (2054901185843/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1247; no trusted numerical premise.
theorem cover8_leaf1247_exp_radius : (997994529213163443/1000000000000000000 : ℝ) ≤ Real.exp ((-2105/131072 : ℝ)/8) ∧ Real.exp ((-2105/131072 : ℝ)/8) ≤ (249498632303290861/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2105/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1247_exp_lower : (57507089387848777/62500000000000000 : ℝ) ≤ Real.exp ((-42628261292737/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628261292737/64000000000000 : ℝ)/8) ≤ (920113430205580433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628261292737/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1247_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980243899/200000000000 : ℝ) ≤ 4*Real.exp (33679/262144 : ℝ)*Real.exp (-mu (radius 8 (2105/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410980243899/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2105/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1247_exp_radius
  have hrNumeric : (196813679343/200000000000 : ℝ) ≤ Real.exp (-2105/131072 : ℝ) ∧ Real.exp (-2105/131072 : ℝ) ≤ (246017099179/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196813679343/200000000000 : ℝ) ≤ (radius 8 (2105/16384 : ℝ)) ∧ (radius 8 (2105/16384 : ℝ)) ≤ (246017099179/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2105/16384 : ℝ)) (196813679343/200000000000 : ℝ) (246017099179/250000000000 : ℝ) (177790299467/1000000000000 : ℝ) (88895149737/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2105/16384 : ℝ)) (196813679343/200000000000 : ℝ) (246017099179/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196813679343/200000000000 : ℝ) (246017099179/250000000000 : ℝ) (992034198357/1000000000000 : ℝ) (496017099179/500000000000 : ℝ) (992002216083/1000000000000 : ℝ) (198400443217/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 1 (992034198357/1000000000000 : ℝ) (496017099179/500000000000 : ℝ) (992002216083/1000000000000 : ℝ) (198400443217/200000000000 : ℝ) (49600910361/50000000000 : ℝ) (496009103611/500000000000 : ℝ) (992018207091/1000000000000 : ℝ) (992018207093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 2 (49600910361/50000000000 : ℝ) (496009103611/500000000000 : ℝ) (992018207091/1000000000000 : ℝ) (992018207093/1000000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 3 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 4 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 5 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 6 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2105/16384 : ℝ)) 7 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2105/16384 : ℝ))) (177790299467/1000000000000 : ℝ) (88895149737/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177790299467/1000000000000 : ℝ) (88895149737/500000000000 : ℝ) (588895149733/1000000000000 : ℝ) (588895149737/1000000000000 : ℝ) (421651869991/1000000000000 : ℝ) (42165187/100000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 1 (588895149733/1000000000000 : ℝ) (588895149737/1000000000000 : ℝ) (421651869991/1000000000000 : ℝ) (42165187/100000000 : ℝ) (252636754931/500000000000 : ℝ) (505273509869/1000000000000 : ℝ) (1557205847/3125000000 : ℝ) (62288233881/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 2 (252636754931/500000000000 : ℝ) (505273509869/1000000000000 : ℝ) (1557205847/3125000000 : ℝ) (62288233881/125000000000 : ℝ) (501789690451/1000000000000 : ℝ) (501789690459/1000000000000 : ℝ) (100355519319/200000000000 : ℝ) (125444399151/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 3 (501789690451/1000000000000 : ℝ) (501789690459/1000000000000 : ℝ) (100355519319/200000000000 : ℝ) (125444399151/250000000000 : ℝ) (501783643523/1000000000000 : ℝ) (125445910883/250000000000 : ℝ) (250891821743/500000000000 : ℝ) (62722955437/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 4 (501783643523/1000000000000 : ℝ) (125445910883/250000000000 : ℝ) (250891821743/500000000000 : ℝ) (62722955437/125000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 5 (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 6 (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2105/16384 : ℝ))) 7 (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2105/16384 : ℝ)) hmem 8 (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2105/16384 : ℝ))) hcmem 8 (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2105/16384 : ℝ)) (198403641431/200000000000 : ℝ) (496009103579/500000000000 : ℝ) (31361477719/62500000000 : ℝ) (250891821757/500000000000 : ℝ) (794541771889/1000000000000 : ℝ) (198635442977/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1247_exp_lower
  have heNumeric : (410980243899/200000000000 : ℝ)/4 ≤ Real.exp (-42628261292737/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980243899/200000000000 : ℝ)/4 ≤ Real.exp ((33679/262144 : ℝ)-(198635442977/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33679/262144 : ℝ) (2105/16384 : ℝ) (198635442977/250000000000 : ℝ) (410980243899/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1248; no trusted numerical premise.
theorem cover8_leaf1248_exp_radius : (199598893945611163/200000000000000000 : ℝ) ≤ Real.exp ((-33681/2097152 : ℝ)/8) ∧ Real.exp ((-33681/2097152 : ℝ)/8) ≤ (124749308716006977/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33681/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1248_exp_lower : (920113432098514339/1000000000000000000 : ℝ) ≤ Real.exp ((-2664266264963/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664266264963/4000000000000 : ℝ)/8) ≤ (46005671604925717/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664266264963/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1248_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980250663/200000000000 : ℝ) ≤ 4*Real.exp (2105/16384 : ℝ)*Real.exp (-mu (radius 8 (33681/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980250663/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33681/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1248_exp_radius
  have hrNumeric : (39362717099/40000000000 : ℝ) ≤ Real.exp (-33681/2097152 : ℝ) ∧ Real.exp (-33681/2097152 : ℝ) ≤ (246016981869/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39362717099/40000000000 : ℝ) ≤ (radius 8 (33681/262144 : ℝ)) ∧ (radius 8 (33681/262144 : ℝ)) ≤ (246016981869/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33681/262144 : ℝ)) (39362717099/40000000000 : ℝ) (246016981869/250000000000 : ℝ) (177792896689/1000000000000 : ℝ) (35558579339/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33681/262144 : ℝ)) (39362717099/40000000000 : ℝ) (246016981869/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39362717099/40000000000 : ℝ) (246016981869/250000000000 : ℝ) (992033963737/1000000000000 : ℝ) (496016981869/500000000000 : ℝ) (248000494893/250000000000 : ℝ) (992001979573/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 1 (992033963737/1000000000000 : ℝ) (496016981869/500000000000 : ℝ) (248000494893/250000000000 : ℝ) (992001979573/1000000000000 : ℝ) (496008985827/500000000000 : ℝ) (124002246457/125000000000 : ℝ) (39680718861/40000000000 : ℝ) (992017971527/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 2 (496008985827/500000000000 : ℝ) (124002246457/125000000000 : ℝ) (39680718861/40000000000 : ℝ) (992017971527/1000000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 3 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 4 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 5 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 6 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33681/262144 : ℝ)) 7 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33681/262144 : ℝ))) (177792896689/1000000000000 : ℝ) (35558579339/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177792896689/1000000000000 : ℝ) (35558579339/200000000000 : ℝ) (73612056043/125000000000 : ℝ) (147224112087/250000000000 : ℝ) (421654949797/1000000000000 : ℝ) (84330989961/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 1 (73612056043/125000000000 : ℝ) (147224112087/250000000000 : ℝ) (421654949797/1000000000000 : ℝ) (84330989961/200000000000 : ℝ) (50527569907/100000000000 : ℝ) (505275699077/1000000000000 : ℝ) (498308240311/1000000000000 : ℝ) (249154120159/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 2 (50527569907/100000000000 : ℝ) (505275699077/1000000000000 : ℝ) (498308240311/1000000000000 : ℝ) (249154120159/500000000000 : ℝ) (50179196969/100000000000 : ℝ) (250895984849/500000000000 : ℝ) (100355975303/200000000000 : ℝ) (501779876523/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 3 (50179196969/100000000000 : ℝ) (250895984849/500000000000 : ℝ) (100355975303/200000000000 : ℝ) (501779876523/1000000000000 : ℝ) (250892961551/500000000000 : ℝ) (501785923111/1000000000000 : ℝ) (250892961533/500000000000 : ℝ) (20071436923/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 4 (250892961551/500000000000 : ℝ) (501785923111/1000000000000 : ℝ) (250892961533/500000000000 : ℝ) (20071436923/40000000000 : ℝ) (125446480771/250000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 5 (125446480771/250000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 6 (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33681/262144 : ℝ))) 7 (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33681/262144 : ℝ)) hmem 8 (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33681/262144 : ℝ))) hcmem 8 (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33681/262144 : ℝ)) (992017971589/1000000000000 : ℝ) (124002246449/125000000000 : ℝ) (501785923083/1000000000000 : ℝ) (501785923093/1000000000000 : ℝ) (49659098133/62500000000 : ℝ) (794545570147/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1248_exp_lower
  have heNumeric : (410980250663/200000000000 : ℝ)/4 ≤ Real.exp (-2664266264963/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980250663/200000000000 : ℝ)/4 ≤ Real.exp ((2105/16384 : ℝ)-(794545570147/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2105/16384 : ℝ) (33681/262144 : ℝ) (794545570147/1000000000000 : ℝ) (410980250663/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1249; no trusted numerical premise.
theorem cover8_leaf1249_exp_radius : (997994410242951731/1000000000000000000 : ℝ) ≤ Real.exp ((-16841/1048576 : ℝ)/8) ∧ Real.exp ((-16841/1048576 : ℝ)/8) ≤ (249498602560737933/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16841/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1249_exp_lower : (920113433999959299/1000000000000000000 : ℝ) ≤ Real.exp ((-42628259181343/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628259181343/64000000000000 : ℝ)/8) ≤ (9201134339999593/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628259181343/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1249_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901287287/1000000000000 : ℝ) ≤ 4*Real.exp (33681/262144 : ℝ)*Real.exp (-mu (radius 8 (16841/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901287287/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16841/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1249_exp_radius
  have hrNumeric : (196813491647/200000000000 : ℝ) ≤ Real.exp (-16841/1048576 : ℝ) ∧ Real.exp (-16841/1048576 : ℝ) ≤ (246016864559/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196813491647/200000000000 : ℝ) ≤ (radius 8 (16841/131072 : ℝ)) ∧ (radius 8 (16841/131072 : ℝ)) ≤ (246016864559/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16841/131072 : ℝ)) (196813491647/200000000000 : ℝ) (246016864559/250000000000 : ℝ) (177795493871/1000000000000 : ℝ) (177795493877/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16841/131072 : ℝ)) (196813491647/200000000000 : ℝ) (246016864559/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196813491647/200000000000 : ℝ) (246016864559/250000000000 : ℝ) (992033729117/1000000000000 : ℝ) (496016864559/500000000000 : ℝ) (49600087153/50000000000 : ℝ) (992001743061/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 1 (992033729117/1000000000000 : ℝ) (496016864559/500000000000 : ℝ) (49600087153/50000000000 : ℝ) (992001743061/1000000000000 : ℝ) (124002217011/125000000000 : ℝ) (99201773609/100000000000 : ℝ) (992017735959/1000000000000 : ℝ) (992017735961/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 2 (124002217011/125000000000 : ℝ) (99201773609/100000000000 : ℝ) (992017735959/1000000000000 : ℝ) (992017735961/1000000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 3 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 4 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 5 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 6 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16841/131072 : ℝ)) 7 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16841/131072 : ℝ))) (177795493871/1000000000000 : ℝ) (177795493877/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177795493871/1000000000000 : ℝ) (177795493877/1000000000000 : ℝ) (117779549387/200000000000 : ℝ) (588897746939/1000000000000 : ℝ) (210829014767/500000000000 : ℝ) (210829014771/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 1 (117779549387/200000000000 : ℝ) (588897746939/1000000000000 : ℝ) (210829014767/500000000000 : ℝ) (210829014771/500000000000 : ℝ) (252638944117/500000000000 : ℝ) (505277888241/1000000000000 : ℝ) (498310609529/1000000000000 : ℝ) (3893051637/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 2 (252638944117/500000000000 : ℝ) (505277888241/1000000000000 : ℝ) (498310609529/1000000000000 : ℝ) (3893051637/7812500000 : ℝ) (501794248881/1000000000000 : ℝ) (501794248889/1000000000000 : ℝ) (250891078193/500000000000 : ℝ) (250891078197/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 3 (501794248881/1000000000000 : ℝ) (501794248889/1000000000000 : ℝ) (250891078193/500000000000 : ℝ) (250891078197/500000000000 : ℝ) (501788202633/1000000000000 : ℝ) (250894101321/500000000000 : ℝ) (501788202597/1000000000000 : ℝ) (250894101303/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 4 (501788202633/1000000000000 : ℝ) (250894101321/500000000000 : ℝ) (501788202597/1000000000000 : ℝ) (250894101303/500000000000 : ℝ) (100357640523/200000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 5 (100357640523/200000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 6 (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16841/131072 : ℝ))) 7 (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16841/131072 : ℝ)) hmem 8 (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16841/131072 : ℝ))) hcmem 8 (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16841/131072 : ℝ)) (992017736023/1000000000000 : ℝ) (496008868013/500000000000 : ℝ) (250894101307/500000000000 : ℝ) (3920220333/7812500000 : ℝ) (794549368293/1000000000000 : ℝ) (99318671039/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1249_exp_lower
  have heNumeric : (2054901287287/1000000000000 : ℝ)/4 ≤ Real.exp (-42628259181343/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901287287/1000000000000 : ℝ)/4 ≤ Real.exp ((33681/262144 : ℝ)-(99318671039/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33681/262144 : ℝ) (16841/131072 : ℝ) (99318671039/125000000000 : ℝ) (2054901287287/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1225_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1225_certificate
#check SmaleRate.Proofs.cover8_leaf1226_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1226_certificate
#check SmaleRate.Proofs.cover8_leaf1227_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1227_certificate
#check SmaleRate.Proofs.cover8_leaf1228_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1228_certificate
#check SmaleRate.Proofs.cover8_leaf1229_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1229_certificate
#check SmaleRate.Proofs.cover8_leaf1230_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1230_certificate
#check SmaleRate.Proofs.cover8_leaf1231_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1231_certificate
#check SmaleRate.Proofs.cover8_leaf1232_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1232_certificate
#check SmaleRate.Proofs.cover8_leaf1233_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1233_certificate
#check SmaleRate.Proofs.cover8_leaf1234_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1234_certificate
#check SmaleRate.Proofs.cover8_leaf1235_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1235_certificate
#check SmaleRate.Proofs.cover8_leaf1236_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1236_certificate
#check SmaleRate.Proofs.cover8_leaf1237_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1237_certificate
#check SmaleRate.Proofs.cover8_leaf1238_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1238_certificate
#check SmaleRate.Proofs.cover8_leaf1239_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1239_certificate
#check SmaleRate.Proofs.cover8_leaf1240_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1240_certificate
#check SmaleRate.Proofs.cover8_leaf1241_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1241_certificate
#check SmaleRate.Proofs.cover8_leaf1242_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1242_certificate
#check SmaleRate.Proofs.cover8_leaf1243_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1243_certificate
#check SmaleRate.Proofs.cover8_leaf1244_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1244_certificate
#check SmaleRate.Proofs.cover8_leaf1245_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1245_certificate
#check SmaleRate.Proofs.cover8_leaf1246_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1246_certificate
#check SmaleRate.Proofs.cover8_leaf1247_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1247_certificate
#check SmaleRate.Proofs.cover8_leaf1248_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1248_certificate
#check SmaleRate.Proofs.cover8_leaf1249_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1249_certificate
