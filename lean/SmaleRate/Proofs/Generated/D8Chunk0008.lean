/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0200; no trusted numerical premise.
theorem cover8_leaf0200_exp_radius : (998046163623812863/1000000000000000000 : ℝ) ≤ Real.exp ((-8203/524288 : ℝ)/8) ∧ Real.exp ((-8203/524288 : ℝ)/8) ≤ (3898617826655519/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-8203/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0200_exp_lower : (184022767750902019/200000000000000000 : ℝ) ≤ Real.exp ((-5328504244307/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328504244307/8000000000000 : ℝ)/8) ≤ (57507114922156881/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328504244307/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0200_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908518847/1000000000000 : ℝ) ≤ 4*Real.exp (4101/32768 : ℝ)*Real.exp (-mu (radius 8 (8203/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908518847/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8203/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0200_exp_radius
  have hrNumeric : (30764868177/31250000000 : ℝ) ≤ Real.exp (-8203/524288 : ℝ) ∧ Real.exp (-8203/524288 : ℝ) ≤ (196895156333/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30764868177/31250000000 : ℝ) ≤ (radius 8 (8203/65536 : ℝ)) ∧ (radius 8 (8203/65536 : ℝ)) ≤ (196895156333/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8203/65536 : ℝ)) (30764868177/31250000000 : ℝ) (196895156333/200000000000 : ℝ) (175520469789/1000000000000 : ℝ) (35104093959/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8203/65536 : ℝ)) (30764868177/31250000000 : ℝ) (196895156333/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30764868177/31250000000 : ℝ) (196895156333/200000000000 : ℝ) (62014868177/62500000000 : ℝ) (992237890833/1000000000000 : ℝ) (496103764767/500000000000 : ℝ) (198441505907/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 1 (62014868177/62500000000 : ℝ) (992237890833/1000000000000 : ℝ) (496103764767/500000000000 : ℝ) (198441505907/200000000000 : ℝ) (992222710183/1000000000000 : ℝ) (124027838773/125000000000 : ℝ) (496111355033/500000000000 : ℝ) (248055677517/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 2 (992222710183/1000000000000 : ℝ) (124027838773/125000000000 : ℝ) (496111355033/500000000000 : ℝ) (248055677517/250000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 3 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 4 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 5 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 6 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8203/65536 : ℝ)) 7 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8203/65536 : ℝ))) (175520469789/1000000000000 : ℝ) (35104093959/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175520469789/1000000000000 : ℝ) (35104093959/200000000000 : ℝ) (293880117447/500000000000 : ℝ) (293880117449/500000000000 : ℝ) (418951631801/1000000000000 : ℝ) (418951631809/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 1 (293880117447/500000000000 : ℝ) (293880117449/500000000000 : ℝ) (418951631801/1000000000000 : ℝ) (418951631809/1000000000000 : ℝ) (503355933347/1000000000000 : ℝ) (251677966677/500000000000 : ℝ) (62028611029/125000000000 : ℝ) (6202861103/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 2 (503355933347/1000000000000 : ℝ) (251677966677/500000000000 : ℝ) (62028611029/125000000000 : ℝ) (6202861103/12500000000 : ℝ) (499792410789/1000000000000 : ℝ) (499792410797/1000000000000 : ℝ) (24988985333/50000000000 : ℝ) (499779706669/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 3 (499792410789/1000000000000 : ℝ) (499792410797/1000000000000 : ℝ) (24988985333/50000000000 : ℝ) (499779706669/1000000000000 : ℝ) (124946514681/250000000000 : ℝ) (499786058733/1000000000000 : ℝ) (124946514671/250000000000 : ℝ) (499786058693/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 4 (124946514681/250000000000 : ℝ) (499786058733/1000000000000 : ℝ) (124946514671/250000000000 : ℝ) (499786058693/1000000000000 : ℝ) (31236628669/62500000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 5 (31236628669/62500000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 6 (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8203/65536 : ℝ))) 7 (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8203/65536 : ℝ)) hmem 8 (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8203/65536 : ℝ))) hcmem 8 (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8203/65536 : ℝ)) (248055677531/250000000000 : ℝ) (496111355063/500000000000 : ℝ) (499786058703/1000000000000 : ℝ) (499786058713/1000000000000 : ℝ) (791215618411/1000000000000 : ℝ) (791215618429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0200_exp_lower
  have heNumeric : (2054908518847/1000000000000 : ℝ)/4 ≤ Real.exp (-5328504244307/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908518847/1000000000000 : ℝ)/4 ≤ Real.exp ((4101/32768 : ℝ)-(791215618429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4101/32768 : ℝ) (8203/65536 : ℝ) (791215618429/1000000000000 : ℝ) (2054908518847/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0201; no trusted numerical premise.
theorem cover8_leaf0201_exp_radius : (49902296283554651/50000000000000000 : ℝ) ≤ Real.exp ((-2051/131072 : ℝ)/8) ∧ Real.exp ((-2051/131072 : ℝ)/8) ≤ (998045925671093021/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2051/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0201_exp_lower : (920113815140946057/1000000000000000000 : ℝ) ≤ Real.exp ((-10657011773573/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657011773573/16000000000000 : ℝ)/8) ≤ (460056907570473029/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657011773573/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0201_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454048477/500000000000 : ℝ) ≤ 4*Real.exp (8203/65536 : ℝ)*Real.exp (-mu (radius 8 (2051/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454048477/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2051/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0201_exp_radius
  have hrNumeric : (123059237991/125000000000 : ℝ) ≤ Real.exp (-2051/131072 : ℝ) ∧ Real.exp (-2051/131072 : ℝ) ≤ (984473903929/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123059237991/125000000000 : ℝ) ≤ (radius 8 (2051/16384 : ℝ)) ∧ (radius 8 (2051/16384 : ℝ)) ≤ (984473903929/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2051/16384 : ℝ)) (123059237991/125000000000 : ℝ) (984473903929/1000000000000 : ℝ) (87765500743/500000000000 : ℝ) (43882750373/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2051/16384 : ℝ)) (123059237991/125000000000 : ℝ) (984473903929/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123059237991/125000000000 : ℝ) (984473903929/1000000000000 : ℝ) (248059237991/250000000000 : ℝ) (198447390393/200000000000 : ℝ) (248051645823/250000000000 : ℝ) (992206583293/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 1 (248059237991/250000000000 : ℝ) (198447390393/200000000000 : ℝ) (248051645823/250000000000 : ℝ) (992206583293/1000000000000 : ℝ) (248055441907/250000000000 : ℝ) (992221767629/1000000000000 : ℝ) (992221767511/1000000000000 : ℝ) (992221767513/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 2 (248055441907/250000000000 : ℝ) (992221767629/1000000000000 : ℝ) (992221767511/1000000000000 : ℝ) (992221767513/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 3 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 4 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 5 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 6 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2051/16384 : ℝ)) 7 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2051/16384 : ℝ))) (87765500743/500000000000 : ℝ) (43882750373/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87765500743/500000000000 : ℝ) (43882750373/250000000000 : ℝ) (587765500743/1000000000000 : ℝ) (293882750373/500000000000 : ℝ) (418964200721/1000000000000 : ℝ) (418964200729/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 1 (587765500743/1000000000000 : ℝ) (293882750373/500000000000 : ℝ) (418964200721/1000000000000 : ℝ) (418964200729/1000000000000 : ℝ) (125841212683/250000000000 : ℝ) (251682425369/500000000000 : ℝ) (496238554759/1000000000000 : ℝ) (248119277383/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 2 (125841212683/250000000000 : ℝ) (251682425369/500000000000 : ℝ) (496238554759/1000000000000 : ℝ) (248119277383/500000000000 : ℝ) (99960340549/200000000000 : ℝ) (15618803211/31250000000 : ℝ) (499789001523/1000000000000 : ℝ) (49978900153/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 3 (99960340549/200000000000 : ℝ) (15618803211/31250000000 : ℝ) (499789001523/1000000000000 : ℝ) (49978900153/100000000000 : ℝ) (249897676067/500000000000 : ℝ) (499795352141/1000000000000 : ℝ) (499795352093/1000000000000 : ℝ) (499795352101/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 4 (249897676067/500000000000 : ℝ) (499795352141/1000000000000 : ℝ) (499795352093/1000000000000 : ℝ) (499795352101/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 5 (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 6 (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2051/16384 : ℝ))) 7 (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2051/16384 : ℝ)) hmem 8 (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2051/16384 : ℝ))) hcmem 8 (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2051/16384 : ℝ)) (992221767569/1000000000000 : ℝ) (992221767571/1000000000000 : ℝ) (499795352113/1000000000000 : ℝ) (499795352121/1000000000000 : ℝ) (791231082513/1000000000000 : ℝ) (24725971329/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0201_exp_lower
  have heNumeric : (1027454048477/500000000000 : ℝ)/4 ≤ Real.exp (-10657011773573/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454048477/500000000000 : ℝ)/4 ≤ Real.exp ((8203/65536 : ℝ)-(24725971329/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8203/65536 : ℝ) (2051/16384 : ℝ) (24725971329/31250000000 : ℝ) (1027454048477/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0202; no trusted numerical premise.
theorem cover8_leaf0202_exp_radius : (99804568771842991/100000000000000000 : ℝ) ≤ Real.exp ((-8205/524288 : ℝ)/8) ∧ Real.exp ((-8205/524288 : ℝ)/8) ≤ (998045687718429911/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8205/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0202_exp_lower : (230028447918190151/250000000000000000 : ℝ) ≤ Real.exp ((-2664253759577/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664253759577/4000000000000 : ℝ)/8) ≤ (184022758334552121/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664253759577/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0202_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907677659/1000000000000 : ℝ) ≤ 4*Real.exp (2051/16384 : ℝ)*Real.exp (-mu (radius 8 (8205/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907677659/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8205/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0202_exp_radius
  have hrNumeric : (492236013097/500000000000 : ℝ) ≤ Real.exp (-8205/524288 : ℝ) ∧ Real.exp (-8205/524288 : ℝ) ≤ (196894405239/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492236013097/500000000000 : ℝ) ≤ (radius 8 (8205/65536 : ℝ)) ∧ (radius 8 (8205/65536 : ℝ)) ≤ (196894405239/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8205/65536 : ℝ)) (492236013097/500000000000 : ℝ) (196894405239/200000000000 : ℝ) (4388538313/25000000000 : ℝ) (87770766263/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8205/65536 : ℝ)) (492236013097/500000000000 : ℝ) (196894405239/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492236013097/500000000000 : ℝ) (196894405239/200000000000 : ℝ) (992236013097/1000000000000 : ℝ) (496118006549/500000000000 : ℝ) (19844112741/20000000000 : ℝ) (992205637051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 1 (992236013097/1000000000000 : ℝ) (496118006549/500000000000 : ℝ) (19844112741/20000000000 : ℝ) (992205637051/1000000000000 : ℝ) (992220825073/1000000000000 : ℝ) (39688833003/40000000000 : ℝ) (992220824957/1000000000000 : ℝ) (992220824959/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 2 (992220825073/1000000000000 : ℝ) (39688833003/40000000000 : ℝ) (992220824957/1000000000000 : ℝ) (992220824959/1000000000000 : ℝ) (198444165003/200000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 3 (198444165003/200000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 4 (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 5 (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 6 (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8205/65536 : ℝ)) 7 (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8205/65536 : ℝ))) (4388538313/25000000000 : ℝ) (87770766263/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4388538313/25000000000 : ℝ) (87770766263/500000000000 : ℝ) (29388538313/50000000000 : ℝ) (587770766263/1000000000000 : ℝ) (52372096059/125000000000 : ℝ) (418976768481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 1 (29388538313/50000000000 : ℝ) (587770766263/1000000000000 : ℝ) (52372096059/125000000000 : ℝ) (418976768481/1000000000000 : ℝ) (251686883683/500000000000 : ℝ) (125843441843/250000000000 : ℝ) (496248220399/1000000000000 : ℝ) (496248220407/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 2 (251686883683/500000000000 : ℝ) (125843441843/250000000000 : ℝ) (496248220399/1000000000000 : ℝ) (496248220407/1000000000000 : ℝ) (249905496941/500000000000 : ℝ) (49981099389/100000000000 : ℝ) (249899147783/500000000000 : ℝ) (249899147787/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 3 (249905496941/500000000000 : ℝ) (49981099389/100000000000 : ℝ) (249899147783/500000000000 : ℝ) (249899147787/500000000000 : ℝ) (124951161181/250000000000 : ℝ) (124951161183/250000000000 : ℝ) (499804644683/1000000000000 : ℝ) (124951161173/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 4 (124951161181/250000000000 : ℝ) (124951161183/250000000000 : ℝ) (499804644683/1000000000000 : ℝ) (124951161173/250000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 5 (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 6 (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8205/65536 : ℝ))) 7 (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8205/65536 : ℝ)) hmem 8 (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8205/65536 : ℝ))) hcmem 8 (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8205/65536 : ℝ)) (496110412507/500000000000 : ℝ) (992220825017/1000000000000 : ℝ) (499804644703/1000000000000 : ℝ) (62475580589/125000000000 : ℝ) (158249309069/200000000000 : ℝ) (791246545363/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0202_exp_lower
  have heNumeric : (2054907677659/1000000000000 : ℝ)/4 ≤ Real.exp (-2664253759577/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907677659/1000000000000 : ℝ)/4 ≤ Real.exp ((2051/16384 : ℝ)-(791246545363/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2051/16384 : ℝ) (8205/65536 : ℝ) (791246545363/1000000000000 : ℝ) (2054907677659/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0203; no trusted numerical premise.
theorem cover8_leaf0203_exp_radius : (249511362441455883/250000000000000000 : ℝ) ≤ Real.exp ((-4103/262144 : ℝ)/8) ∧ Real.exp ((-4103/262144 : ℝ)/8) ≤ (998045449765823533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4103/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0203_exp_lower : (460056884176644569/500000000000000000 : ℝ) ≤ Real.exp ((-2131403656471/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131403656471/3200000000000 : ℝ)/8) ≤ (920113768353289139/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131403656471/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0203_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745363051/50000000000 : ℝ) ≤ 4*Real.exp (8205/65536 : ℝ)*Real.exp (-mu (radius 8 (4103/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102745363051/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4103/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0203_exp_radius
  have hrNumeric : (196894029693/200000000000 : ℝ) ≤ Real.exp (-4103/262144 : ℝ) ∧ Real.exp (-4103/262144 : ℝ) ≤ (492235074233/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196894029693/200000000000 : ℝ) ≤ (radius 8 (4103/32768 : ℝ)) ∧ (radius 8 (4103/32768 : ℝ)) ≤ (492235074233/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4103/32768 : ℝ)) (196894029693/200000000000 : ℝ) (492235074233/500000000000 : ℝ) (87776031437/500000000000 : ℝ) (1097200393/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4103/32768 : ℝ)) (196894029693/200000000000 : ℝ) (492235074233/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196894029693/200000000000 : ℝ) (492235074233/500000000000 : ℝ) (124029384279/125000000000 : ℝ) (992235074233/1000000000000 : ℝ) (992204690809/1000000000000 : ℝ) (992204690811/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 1 (124029384279/125000000000 : ℝ) (992235074233/1000000000000 : ℝ) (992204690809/1000000000000 : ℝ) (992204690811/1000000000000 : ℝ) (24805497063/25000000000 : ℝ) (496109941261/500000000000 : ℝ) (248054970601/250000000000 : ℝ) (496109941203/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 2 (24805497063/25000000000 : ℝ) (496109941261/500000000000 : ℝ) (248054970601/250000000000 : ℝ) (496109941203/500000000000 : ℝ) (496109941231/500000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 3 (496109941231/500000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 4 (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 5 (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 6 (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4103/32768 : ℝ)) 7 (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4103/32768 : ℝ))) (87776031437/500000000000 : ℝ) (1097200393/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87776031437/500000000000 : ℝ) (1097200393/6250000000 : ℝ) (587776031437/1000000000000 : ℝ) (7347200393/12500000000 : ℝ) (104747333759/250000000000 : ℝ) (104747333761/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 1 (587776031437/1000000000000 : ℝ) (7347200393/12500000000 : ℝ) (104747333759/250000000000 : ℝ) (104747333761/250000000000 : ℝ) (125845670809/250000000000 : ℝ) (251691341621/500000000000 : ℝ) (248128942569/500000000000 : ℝ) (99251577029/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 2 (125845670809/250000000000 : ℝ) (251691341621/500000000000 : ℝ) (248128942569/500000000000 : ℝ) (99251577029/200000000000 : ℝ) (499820284187/1000000000000 : ℝ) (249910142097/500000000000 : ℝ) (19992303551/40000000000 : ℝ) (499807588783/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 3 (499820284187/1000000000000 : ℝ) (249910142097/500000000000 : ℝ) (19992303551/40000000000 : ℝ) (499807588783/1000000000000 : ℝ) (499813936481/1000000000000 : ℝ) (499813936489/1000000000000 : ℝ) (12495348411/25000000000 : ℝ) (499813936449/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 4 (499813936481/1000000000000 : ℝ) (499813936489/1000000000000 : ℝ) (12495348411/25000000000 : ℝ) (499813936449/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 5 (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 6 (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4103/32768 : ℝ))) 7 (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4103/32768 : ℝ)) hmem 8 (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4103/32768 : ℝ))) hcmem 8 (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4103/32768 : ℝ)) (992219882461/1000000000000 : ℝ) (31006871327/31250000000 : ℝ) (24990696823/50000000000 : ℝ) (499813936469/1000000000000 : ℝ) (791262006887/1000000000000 : ℝ) (158252401381/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0203_exp_lower
  have heNumeric : (102745363051/50000000000 : ℝ)/4 ≤ Real.exp (-2131403656471/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745363051/50000000000 : ℝ)/4 ≤ Real.exp ((8205/65536 : ℝ)-(158252401381/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8205/65536 : ℝ) (4103/32768 : ℝ) (158252401381/200000000000 : ℝ) (102745363051/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0204; no trusted numerical premise.
theorem cover8_leaf0204_exp_radius : (499022605906636943/500000000000000000 : ℝ) ≤ Real.exp ((-8207/524288 : ℝ)/8) ∧ Real.exp ((-8207/524288 : ℝ)/8) ≤ (998045211813273887/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8207/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0204_exp_lower : (920113745180691419/1000000000000000000 : ℝ) ≤ Real.exp ((-1065702150597/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065702150597/1600000000000 : ℝ)/8) ≤ (46005687259034571/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065702150597/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0204_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453423503/500000000000 : ℝ) ≤ 4*Real.exp (4103/32768 : ℝ)*Real.exp (-mu (radius 8 (8207/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453423503/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8207/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0204_exp_radius
  have hrNumeric : (984468270739/1000000000000 : ℝ) ≤ Real.exp (-8207/524288 : ℝ) ∧ Real.exp (-8207/524288 : ℝ) ≤ (49223413537/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984468270739/1000000000000 : ℝ) ≤ (radius 8 (8207/65536 : ℝ)) ∧ (radius 8 (8207/65536 : ℝ)) ≤ (49223413537/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8207/65536 : ℝ)) (984468270739/1000000000000 : ℝ) (49223413537/50000000000 : ℝ) (175562592559/1000000000000 : ℝ) (87781296283/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8207/65536 : ℝ)) (984468270739/1000000000000 : ℝ) (49223413537/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984468270739/1000000000000 : ℝ) (49223413537/50000000000 : ℝ) (992234135369/1000000000000 : ℝ) (99223413537/100000000000 : ℝ) (99220374457/100000000000 : ℝ) (992203744571/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 1 (992234135369/1000000000000 : ℝ) (99223413537/100000000000 : ℝ) (99220374457/100000000000 : ℝ) (992203744571/1000000000000 : ℝ) (992218939969/1000000000000 : ℝ) (992218939971/1000000000000 : ℝ) (992218939853/1000000000000 : ℝ) (198443787971/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 2 (992218939969/1000000000000 : ℝ) (992218939971/1000000000000 : ℝ) (992218939853/1000000000000 : ℝ) (198443787971/200000000000 : ℝ) (992218939911/1000000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 3 (992218939911/1000000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 4 (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 5 (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 6 (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8207/65536 : ℝ)) 7 (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8207/65536 : ℝ))) (175562592559/1000000000000 : ℝ) (87781296283/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175562592559/1000000000000 : ℝ) (87781296283/500000000000 : ℝ) (587781296279/1000000000000 : ℝ) (587781296283/1000000000000 : ℝ) (52375237553/125000000000 : ℝ) (419001900433/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 1 (587781296279/1000000000000 : ℝ) (587781296283/1000000000000 : ℝ) (52375237553/125000000000 : ℝ) (419001900433/1000000000000 : ℝ) (503391598351/1000000000000 : ℝ) (251695799179/500000000000 : ℝ) (496267548983/1000000000000 : ℝ) (7754180453/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 2 (503391598351/1000000000000 : ℝ) (251695799179/500000000000 : ℝ) (496267548983/1000000000000 : ℝ) (7754180453/15625000000 : ℝ) (499829573667/1000000000000 : ℝ) (19993182947/40000000000 : ℝ) (499816881159/1000000000000 : ℝ) (31238555073/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 3 (499829573667/1000000000000 : ℝ) (19993182947/40000000000 : ℝ) (499816881159/1000000000000 : ℝ) (31238555073/62500000000 : ℝ) (499823227413/1000000000000 : ℝ) (249911613711/500000000000 : ℝ) (124955806843/250000000000 : ℝ) (249911613691/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 4 (499823227413/1000000000000 : ℝ) (249911613711/500000000000 : ℝ) (124955806843/250000000000 : ℝ) (249911613691/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 5 (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 6 (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8207/65536 : ℝ))) 7 (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8207/65536 : ℝ)) hmem 8 (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8207/65536 : ℝ))) hcmem 8 (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8207/65536 : ℝ)) (99221893991/100000000000 : ℝ) (992218939913/1000000000000 : ℝ) (976217241/1953125000 : ℝ) (249911613701/500000000000 : ℝ) (791277467151/1000000000000 : ℝ) (79127746717/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0204_exp_lower
  have heNumeric : (1027453423503/500000000000 : ℝ)/4 ≤ Real.exp (-1065702150597/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453423503/500000000000 : ℝ)/4 ≤ Real.exp ((4103/32768 : ℝ)-(79127746717/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4103/32768 : ℝ) (8207/65536 : ℝ) (79127746717/100000000000 : ℝ) (1027453423503/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0205; no trusted numerical premise.
theorem cover8_leaf0205_exp_radius : (998044973860780973/1000000000000000000 : ℝ) ≤ Real.exp ((-513/32768 : ℝ)/8) ∧ Real.exp ((-513/32768 : ℝ)/8) ≤ (499022486930390487/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-513/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0205_exp_lower : (460056861077311197/500000000000000000 : ℝ) ≤ Real.exp ((-10657024709201/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657024709201/16000000000000 : ℝ)/8) ≤ (184022744430924479/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657024709201/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0205_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906435609/1000000000000 : ℝ) ≤ 4*Real.exp (8207/65536 : ℝ)*Real.exp (-mu (radius 8 (513/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906435609/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (513/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0205_exp_radius
  have hrNumeric : (123058299127/125000000000 : ℝ) ≤ Real.exp (-513/32768 : ℝ) ∧ Real.exp (-513/32768 : ℝ) ≤ (984466393017/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123058299127/125000000000 : ℝ) ≤ (radius 8 (513/4096 : ℝ)) ∧ (radius 8 (513/4096 : ℝ)) ≤ (984466393017/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (513/4096 : ℝ)) (123058299127/125000000000 : ℝ) (984466393017/1000000000000 : ℝ) (21946640197/125000000000 : ℝ) (175573121583/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (513/4096 : ℝ)) (123058299127/125000000000 : ℝ) (984466393017/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (513/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123058299127/125000000000 : ℝ) (984466393017/1000000000000 : ℝ) (248058299127/250000000000 : ℝ) (992233196509/1000000000000 : ℝ) (992202798331/1000000000000 : ℝ) (248050699583/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (513/4096 : ℝ)) 1 (248058299127/250000000000 : ℝ) (992233196509/1000000000000 : ℝ) (992202798331/1000000000000 : ℝ) (248050699583/250000000000 : ℝ) (992217997419/1000000000000 : ℝ) (992217997421/1000000000000 : ℝ) (992217997303/1000000000000 : ℝ) (198443599461/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (513/4096 : ℝ)) 2 (992217997419/1000000000000 : ℝ) (992217997421/1000000000000 : ℝ) (992217997303/1000000000000 : ℝ) (198443599461/200000000000 : ℝ) (992217997361/1000000000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (513/4096 : ℝ)) 3 (992217997361/1000000000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (513/4096 : ℝ)) 4 (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (513/4096 : ℝ)) 5 (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (513/4096 : ℝ)) 6 (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (513/4096 : ℝ)) 7 (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (513/4096 : ℝ))) (21946640197/125000000000 : ℝ) (175573121583/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21946640197/125000000000 : ℝ) (175573121583/1000000000000 : ℝ) (146946640197/250000000000 : ℝ) (73473320099/125000000000 : ℝ) (209507232319/500000000000 : ℝ) (419014464647/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 1 (146946640197/250000000000 : ℝ) (73473320099/125000000000 : ℝ) (209507232319/500000000000 : ℝ) (419014464647/1000000000000 : ℝ) (503400512713/1000000000000 : ℝ) (6292506409/12500000000 : ℝ) (496277211939/1000000000000 : ℝ) (496277211947/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 2 (503400512713/1000000000000 : ℝ) (6292506409/12500000000 : ℝ) (496277211939/1000000000000 : ℝ) (496277211947/1000000000000 : ℝ) (249919431163/500000000000 : ℝ) (249919431167/500000000000 : ℝ) (499826172721/1000000000000 : ℝ) (49982617273/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 3 (249919431163/500000000000 : ℝ) (249919431167/500000000000 : ℝ) (499826172721/1000000000000 : ℝ) (49982617273/100000000000 : ℝ) (499832517523/1000000000000 : ℝ) (124958129383/250000000000 : ℝ) (499832517483/1000000000000 : ℝ) (124958129373/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 4 (499832517523/1000000000000 : ℝ) (124958129383/250000000000 : ℝ) (499832517483/1000000000000 : ℝ) (124958129373/250000000000 : ℝ) (499832517503/1000000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 5 (499832517503/1000000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 6 (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (513/4096 : ℝ))) 7 (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (513/4096 : ℝ)) hmem 8 (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (513/4096 : ℝ))) hcmem 8 (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (513/4096 : ℝ)) (12402724967/12500000000 : ℝ) (992217997363/1000000000000 : ℝ) (249916258751/500000000000 : ℝ) (62479064689/125000000000 : ℝ) (395646463071/500000000000 : ℝ) (791292926161/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0205_exp_lower
  have heNumeric : (2054906435609/1000000000000 : ℝ)/4 ≤ Real.exp (-10657024709201/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906435609/1000000000000 : ℝ)/4 ≤ Real.exp ((8207/65536 : ℝ)-(791292926161/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8207/65536 : ℝ) (513/4096 : ℝ) (791292926161/1000000000000 : ℝ) (2054906435609/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0206; no trusted numerical premise.
theorem cover8_leaf0206_exp_radius : (998044735908344791/1000000000000000000 : ℝ) ≤ Real.exp ((-8209/524288 : ℝ)/8) ∧ Real.exp ((-8209/524288 : ℝ)/8) ≤ (124755591988543099/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8209/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0206_exp_lower : (920113699277152307/1000000000000000000 : ℝ) ≤ Real.exp ((-133212848647/200000000000 : ℝ)/8) ∧ Real.exp ((-133212848647/200000000000 : ℝ)/8) ≤ (230028424819288077/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133212848647/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0206_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726506717/250000000000 : ℝ) ≤ 4*Real.exp (513/4096 : ℝ)*Real.exp (-mu (radius 8 (8209/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726506717/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8209/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0206_exp_radius
  have hrNumeric : (492232257649/500000000000 : ℝ) ≤ Real.exp (-8209/524288 : ℝ) ∧ Real.exp (-8209/524288 : ℝ) ≤ (984464515299/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492232257649/500000000000 : ℝ) ≤ (radius 8 (8209/65536 : ℝ)) ∧ (radius 8 (8209/65536 : ℝ)) ≤ (984464515299/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8209/65536 : ℝ)) (492232257649/500000000000 : ℝ) (984464515299/1000000000000 : ℝ) (175583649913/1000000000000 : ℝ) (274349453/1562500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8209/65536 : ℝ)) (492232257649/500000000000 : ℝ) (984464515299/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492232257649/500000000000 : ℝ) (984464515299/1000000000000 : ℝ) (992232257649/1000000000000 : ℝ) (19844645153/20000000000 : ℝ) (992201852093/1000000000000 : ℝ) (198440370419/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 1 (992232257649/1000000000000 : ℝ) (19844645153/20000000000 : ℝ) (992201852093/1000000000000 : ℝ) (198440370419/200000000000 : ℝ) (992217054871/1000000000000 : ℝ) (992217054873/1000000000000 : ℝ) (496108527377/500000000000 : ℝ) (992217054757/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 2 (992217054871/1000000000000 : ℝ) (992217054873/1000000000000 : ℝ) (496108527377/500000000000 : ℝ) (992217054757/1000000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 3 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 4 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 5 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 6 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8209/65536 : ℝ)) 7 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8209/65536 : ℝ))) (175583649913/1000000000000 : ℝ) (274349453/1562500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175583649913/1000000000000 : ℝ) (274349453/1562500000 : ℝ) (146947956239/250000000000 : ℝ) (1836849453/3125000000 : ℝ) (26189189229/62500000000 : ℝ) (419027027673/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 1 (146947956239/250000000000 : ℝ) (1836849453/3125000000 : ℝ) (26189189229/62500000000 : ℝ) (419027027673/1000000000000 : ℝ) (50340942631/100000000000 : ℝ) (503409426317/1000000000000 : ℝ) (496286873991/1000000000000 : ℝ) (496286873999/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 2 (50340942631/100000000000 : ℝ) (503409426317/1000000000000 : ℝ) (496286873991/1000000000000 : ℝ) (496286873999/1000000000000 : ℝ) (9996963003/20000000000 : ℝ) (249924075079/500000000000 : ℝ) (62479432931/125000000000 : ℝ) (499835463457/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 3 (9996963003/20000000000 : ℝ) (249924075079/500000000000 : ℝ) (62479432931/125000000000 : ℝ) (499835463457/1000000000000 : ℝ) (499841806799/1000000000000 : ℝ) (62480225851/125000000000 : ℝ) (249920903379/500000000000 : ℝ) (31240112923/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 4 (499841806799/1000000000000 : ℝ) (62480225851/125000000000 : ℝ) (249920903379/500000000000 : ℝ) (31240112923/62500000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 5 (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 6 (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8209/65536 : ℝ))) 7 (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8209/65536 : ℝ)) hmem 8 (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8209/65536 : ℝ))) hcmem 8 (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8209/65536 : ℝ)) (248054263703/250000000000 : ℝ) (198443410963/200000000000 : ℝ) (249920903389/500000000000 : ℝ) (124960451697/250000000000 : ℝ) (791308383841/1000000000000 : ℝ) (39565419193/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0206_exp_lower
  have heNumeric : (513726506717/250000000000 : ℝ)/4 ≤ Real.exp (-133212848647/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726506717/250000000000 : ℝ)/4 ≤ Real.exp ((513/4096 : ℝ)-(39565419193/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (513/4096 : ℝ) (8209/65536 : ℝ) (39565419193/50000000000 : ℝ) (513726506717/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0207; no trusted numerical premise.
theorem cover8_leaf0207_exp_radius : (499022248977982671/500000000000000000 : ℝ) ≤ Real.exp ((-4105/262144 : ℝ)/8) ∧ Real.exp ((-4105/262144 : ℝ)/8) ≤ (998044497955965343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4105/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0207_exp_lower : (920113676545290779/1000000000000000000 : ℝ) ≤ Real.exp ((-10657031054063/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657031054063/16000000000000 : ℝ)/8) ≤ (46005683827264539/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657031054063/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0207_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863202591/125000000000 : ℝ) ≤ 4*Real.exp (8209/65536 : ℝ)*Real.exp (-mu (radius 8 (4105/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256863202591/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4105/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0207_exp_radius
  have hrNumeric : (492231318791/500000000000 : ℝ) ≤ Real.exp (-4105/262144 : ℝ) ∧ Real.exp (-4105/262144 : ℝ) ≤ (984462637583/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492231318791/500000000000 : ℝ) ≤ (radius 8 (4105/32768 : ℝ)) ∧ (radius 8 (4105/32768 : ℝ)) ≤ (984462637583/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4105/32768 : ℝ)) (492231318791/500000000000 : ℝ) (984462637583/1000000000000 : ℝ) (43898544397/250000000000 : ℝ) (35118835519/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4105/32768 : ℝ)) (492231318791/500000000000 : ℝ) (984462637583/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492231318791/500000000000 : ℝ) (984462637583/1000000000000 : ℝ) (992231318791/1000000000000 : ℝ) (124028914849/125000000000 : ℝ) (7751569577/7812500000 : ℝ) (992200905857/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 1 (992231318791/1000000000000 : ℝ) (124028914849/125000000000 : ℝ) (7751569577/7812500000 : ℝ) (992200905857/1000000000000 : ℝ) (992216112323/1000000000000 : ℝ) (39688644493/40000000000 : ℝ) (496108056103/500000000000 : ℝ) (62013507013/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 2 (992216112323/1000000000000 : ℝ) (39688644493/40000000000 : ℝ) (496108056103/500000000000 : ℝ) (62013507013/62500000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 3 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 4 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 5 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 6 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4105/32768 : ℝ)) 7 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4105/32768 : ℝ))) (43898544397/250000000000 : ℝ) (35118835519/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43898544397/250000000000 : ℝ) (35118835519/200000000000 : ℝ) (293898544397/500000000000 : ℝ) (293898544399/500000000000 : ℝ) (419039589523/1000000000000 : ℝ) (104759897383/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 1 (293898544397/500000000000 : ℝ) (293898544399/500000000000 : ℝ) (419039589523/1000000000000 : ℝ) (104759897383/250000000000 : ℝ) (251709169579/500000000000 : ℝ) (100683667833/200000000000 : ℝ) (496296535159/1000000000000 : ℝ) (496296535167/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 2 (251709169579/500000000000 : ℝ) (100683667833/200000000000 : ℝ) (496296535159/1000000000000 : ℝ) (496296535167/1000000000000 : ℝ) (249928718579/500000000000 : ℝ) (249928718583/500000000000 : ℝ) (249922376679/500000000000 : ℝ) (249922376683/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 3 (249928718579/500000000000 : ℝ) (249928718583/500000000000 : ℝ) (249922376679/500000000000 : ℝ) (249922376683/500000000000 : ℝ) (249925547629/500000000000 : ℝ) (249925547633/500000000000 : ℝ) (499851095217/1000000000000 : ℝ) (249925547613/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 4 (249925547629/500000000000 : ℝ) (249925547633/500000000000 : ℝ) (499851095217/1000000000000 : ℝ) (249925547613/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 5 (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 6 (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4105/32768 : ℝ))) 7 (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4105/32768 : ℝ)) hmem 8 (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4105/32768 : ℝ))) hcmem 8 (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4105/32768 : ℝ)) (124027014033/125000000000 : ℝ) (992216112267/1000000000000 : ℝ) (499851095237/1000000000000 : ℝ) (249925547623/500000000000 : ℝ) (31652953611/40000000000 : ℝ) (791323840293/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0207_exp_lower
  have heNumeric : (256863202591/125000000000 : ℝ)/4 ≤ Real.exp (-10657031054063/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863202591/125000000000 : ℝ)/4 ≤ Real.exp ((8209/65536 : ℝ)-(791323840293/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8209/65536 : ℝ) (4105/32768 : ℝ) (791323840293/1000000000000 : ℝ) (256863202591/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0208; no trusted numerical premise.
theorem cover8_leaf0208_exp_radius : (499022130001821313/500000000000000000 : ℝ) ≤ Real.exp ((-8211/524288 : ℝ)/8) ∧ Real.exp ((-8211/524288 : ℝ)/8) ≤ (998044260003642627/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8211/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0208_exp_lower : (920113653961568111/1000000000000000000 : ℝ) ≤ Real.exp ((-5328517097879/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328517097879/8000000000000 : ℝ)/8) ≤ (57507103372598007/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328517097879/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0208_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726304309/250000000000 : ℝ) ≤ 4*Real.exp (4105/32768 : ℝ)*Real.exp (-mu (radius 8 (8211/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726304309/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8211/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0208_exp_radius
  have hrNumeric : (984460759871/1000000000000 : ℝ) ≤ Real.exp (-8211/524288 : ℝ) ∧ Real.exp (-8211/524288 : ℝ) ≤ (15382199373/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984460759871/1000000000000 : ℝ) ≤ (radius 8 (8211/65536 : ℝ)) ∧ (radius 8 (8211/65536 : ℝ)) ≤ (15382199373/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8211/65536 : ℝ)) (984460759871/1000000000000 : ℝ) (15382199373/15625000000 : ℝ) (21950588073/125000000000 : ℝ) (175604704591/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8211/65536 : ℝ)) (984460759871/1000000000000 : ℝ) (15382199373/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984460759871/1000000000000 : ℝ) (15382199373/15625000000 : ℝ) (198446075987/200000000000 : ℝ) (31007199373/31250000000 : ℝ) (49609997981/50000000000 : ℝ) (496099979811/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 1 (198446075987/200000000000 : ℝ) (31007199373/31250000000 : ℝ) (49609997981/50000000000 : ℝ) (496099979811/500000000000 : ℝ) (992215169777/1000000000000 : ℝ) (992215169779/1000000000000 : ℝ) (49610758483/50000000000 : ℝ) (992215169663/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 2 (992215169777/1000000000000 : ℝ) (992215169779/1000000000000 : ℝ) (49610758483/50000000000 : ℝ) (992215169663/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 3 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 4 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 5 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 6 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8211/65536 : ℝ)) 7 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8211/65536 : ℝ))) (21950588073/125000000000 : ℝ) (175604704591/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21950588073/125000000000 : ℝ) (175604704591/1000000000000 : ℝ) (146950588073/250000000000 : ℝ) (73475294037/125000000000 : ℝ) (104763037549/250000000000 : ℝ) (83810430041/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 1 (146950588073/250000000000 : ℝ) (73475294037/125000000000 : ℝ) (104763037549/250000000000 : ℝ) (83810430041/200000000000 : ℝ) (125856812811/250000000000 : ℝ) (503427251251/1000000000000 : ℝ) (19852247817/40000000000 : ℝ) (248153097717/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 2 (125856812811/250000000000 : ℝ) (503427251251/1000000000000 : ℝ) (19852247817/40000000000 : ℝ) (248153097717/500000000000 : ℝ) (249933361667/500000000000 : ℝ) (499866723343/1000000000000 : ℝ) (249927021217/500000000000 : ℝ) (499854042443/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 3 (249933361667/500000000000 : ℝ) (499866723343/1000000000000 : ℝ) (249927021217/500000000000 : ℝ) (499854042443/1000000000000 : ℝ) (124965095721/250000000000 : ℝ) (499860382893/1000000000000 : ℝ) (499860382843/1000000000000 : ℝ) (499860382853/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 4 (124965095721/250000000000 : ℝ) (499860382893/1000000000000 : ℝ) (499860382843/1000000000000 : ℝ) (499860382853/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 5 (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 6 (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8211/65536 : ℝ))) 7 (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8211/65536 : ℝ)) hmem 8 (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8211/65536 : ℝ))) hcmem 8 (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8211/65536 : ℝ)) (496107584859/500000000000 : ℝ) (992215169721/1000000000000 : ℝ) (499860382863/1000000000000 : ℝ) (499860382873/1000000000000 : ℝ) (791339295419/1000000000000 : ℝ) (395669647719/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0208_exp_lower
  have heNumeric : (513726304309/250000000000 : ℝ)/4 ≤ Real.exp (-5328517097879/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726304309/250000000000 : ℝ)/4 ≤ Real.exp ((4105/32768 : ℝ)-(395669647719/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4105/32768 : ℝ) (8211/65536 : ℝ) (395669647719/500000000000 : ℝ) (513726304309/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0209; no trusted numerical premise.
theorem cover8_leaf0209_exp_radius : (998044022051376641/1000000000000000000 : ℝ) ≤ Real.exp ((-2053/131072 : ℝ)/8) ∧ Real.exp ((-2053/131072 : ℝ)/8) ≤ (499022011025688321/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2053/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0209_exp_lower : (920113631524834149/1000000000000000000 : ℝ) ≤ Real.exp ((-2131407463401/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131407463401/3200000000000 : ℝ)/8) ≤ (18402272630496683/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131407463401/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0209_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904816369/1000000000000 : ℝ) ≤ 4*Real.exp (8211/65536 : ℝ)*Real.exp (-mu (radius 8 (2053/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904816369/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2053/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0209_exp_radius
  have hrNumeric : (984458882163/1000000000000 : ℝ) ≤ Real.exp (-2053/131072 : ℝ) ∧ Real.exp (-2053/131072 : ℝ) ≤ (246114720541/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984458882163/1000000000000 : ℝ) ≤ (radius 8 (2053/16384 : ℝ)) ∧ (radius 8 (2053/16384 : ℝ)) ≤ (246114720541/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2053/16384 : ℝ)) (984458882163/1000000000000 : ℝ) (246114720541/250000000000 : ℝ) (2743987983/15625000000 : ℝ) (87807615459/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2053/16384 : ℝ)) (984458882163/1000000000000 : ℝ) (246114720541/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984458882163/1000000000000 : ℝ) (246114720541/250000000000 : ℝ) (992229441081/1000000000000 : ℝ) (496114720541/500000000000 : ℝ) (198439802677/200000000000 : ℝ) (496099506693/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 1 (992229441081/1000000000000 : ℝ) (496114720541/500000000000 : ℝ) (198439802677/200000000000 : ℝ) (496099506693/500000000000 : ℝ) (992214227233/1000000000000 : ℝ) (496107113617/500000000000 : ℝ) (248053556779/250000000000 : ℝ) (496107113559/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 2 (992214227233/1000000000000 : ℝ) (496107113617/500000000000 : ℝ) (248053556779/250000000000 : ℝ) (496107113559/500000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 3 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 4 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 5 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 6 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2053/16384 : ℝ)) 7 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2053/16384 : ℝ))) (2743987983/15625000000 : ℝ) (87807615459/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2743987983/15625000000 : ℝ) (87807615459/500000000000 : ℝ) (18368987983/31250000000 : ℝ) (587807615459/1000000000000 : ℝ) (83812941939/200000000000 : ℝ) (419064709703/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 1 (18368987983/31250000000 : ℝ) (587807615459/1000000000000 : ℝ) (83812941939/200000000000 : ℝ) (419064709703/1000000000000 : ℝ) (20137446503/40000000000 : ℝ) (503436162581/1000000000000 : ℝ) (496315854801/1000000000000 : ℝ) (62039481851/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 2 (20137446503/40000000000 : ℝ) (503436162581/1000000000000 : ℝ) (496315854801/1000000000000 : ℝ) (62039481851/125000000000 : ℝ) (31242250543/62500000000 : ℝ) (99975201739/200000000000 : ℝ) (499863330687/1000000000000 : ℝ) (99972666139/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 3 (31242250543/62500000000 : ℝ) (99975201739/200000000000 : ℝ) (499863330687/1000000000000 : ℝ) (99972666139/200000000000 : ℝ) (499869669687/1000000000000 : ℝ) (99973933939/200000000000 : ℝ) (499869669647/1000000000000 : ℝ) (99973933931/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 4 (499869669687/1000000000000 : ℝ) (99973933939/200000000000 : ℝ) (499869669647/1000000000000 : ℝ) (99973933931/200000000000 : ℝ) (499869669667/1000000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 5 (499869669667/1000000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 6 (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2053/16384 : ℝ))) 7 (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2053/16384 : ℝ)) hmem 8 (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2053/16384 : ℝ))) hcmem 8 (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2053/16384 : ℝ)) (496107113587/500000000000 : ℝ) (124026778397/125000000000 : ℝ) (249934834833/500000000000 : ℝ) (19994786787/40000000000 : ℝ) (98919343661/125000000000 : ℝ) (158270949861/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0209_exp_lower
  have heNumeric : (2054904816369/1000000000000 : ℝ)/4 ≤ Real.exp (-2131407463401/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904816369/1000000000000 : ℝ)/4 ≤ Real.exp ((8211/65536 : ℝ)-(158270949861/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8211/65536 : ℝ) (2053/16384 : ℝ) (158270949861/200000000000 : ℝ) (2054904816369/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0210; no trusted numerical premise.
theorem cover8_leaf0210_exp_radius : (998043784099167389/1000000000000000000 : ℝ) ≤ Real.exp ((-8213/524288 : ℝ)/8) ∧ Real.exp ((-8213/524288 : ℝ)/8) ≤ (99804378409916739/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8213/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0210_exp_lower : (92011360923416877/100000000000000000 : ℝ) ≤ Real.exp ((-2664260104483/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664260104483/4000000000000 : ℝ)/8) ≤ (920113609234168771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664260104483/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0210_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107881533/15625000000 : ℝ) ≤ 4*Real.exp (2053/16384 : ℝ)*Real.exp (-mu (radius 8 (8213/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (32107881533/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8213/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0210_exp_radius
  have hrNumeric : (492228502229/500000000000 : ℝ) ≤ Real.exp (-8213/524288 : ℝ) ∧ Real.exp (-8213/524288 : ℝ) ≤ (984457004459/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492228502229/500000000000 : ℝ) ≤ (radius 8 (8213/65536 : ℝ)) ∧ (radius 8 (8213/65536 : ℝ)) ≤ (984457004459/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8213/65536 : ℝ)) (492228502229/500000000000 : ℝ) (984457004459/1000000000000 : ℝ) (43906439143/250000000000 : ℝ) (87812878289/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8213/65536 : ℝ)) (492228502229/500000000000 : ℝ) (984457004459/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492228502229/500000000000 : ℝ) (984457004459/1000000000000 : ℝ) (992228502229/1000000000000 : ℝ) (99222850223/100000000000 : ℝ) (19843961343/20000000000 : ℝ) (62012379197/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 1 (992228502229/1000000000000 : ℝ) (99222850223/100000000000 : ℝ) (19843961343/20000000000 : ℝ) (62012379197/62500000000 : ℝ) (992213284689/1000000000000 : ℝ) (992213284691/1000000000000 : ℝ) (248053321143/250000000000 : ℝ) (39688531383/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 2 (992213284689/1000000000000 : ℝ) (992213284691/1000000000000 : ℝ) (248053321143/250000000000 : ℝ) (39688531383/40000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 3 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 4 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 5 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 6 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8213/65536 : ℝ)) 7 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8213/65536 : ℝ))) (43906439143/250000000000 : ℝ) (87812878289/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43906439143/250000000000 : ℝ) (87812878289/500000000000 : ℝ) (293906439143/500000000000 : ℝ) (587812878289/1000000000000 : ℝ) (419077268021/1000000000000 : ℝ) (419077268029/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 1 (293906439143/500000000000 : ℝ) (587812878289/1000000000000 : ℝ) (419077268021/1000000000000 : ℝ) (419077268029/1000000000000 : ℝ) (503445073153/1000000000000 : ℝ) (503445073159/1000000000000 : ℝ) (496325513287/1000000000000 : ℝ) (248162756647/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 2 (503445073153/1000000000000 : ℝ) (503445073159/1000000000000 : ℝ) (496325513287/1000000000000 : ℝ) (248162756647/500000000000 : ℝ) (24994264661/50000000000 : ℝ) (499885293227/1000000000000 : ℝ) (249936309059/500000000000 : ℝ) (799796189/1600000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 3 (24994264661/50000000000 : ℝ) (499885293227/1000000000000 : ℝ) (249936309059/500000000000 : ℝ) (799796189/1600000000 : ℝ) (499878955669/1000000000000 : ℝ) (124969738919/250000000000 : ℝ) (124969738907/250000000000 : ℝ) (124969738909/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 4 (499878955669/1000000000000 : ℝ) (124969738919/250000000000 : ℝ) (124969738907/250000000000 : ℝ) (124969738909/250000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 5 (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 6 (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8213/65536 : ℝ))) 7 (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8213/65536 : ℝ)) hmem 8 (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8213/65536 : ℝ))) hcmem 8 (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8213/65536 : ℝ)) (99221328463/100000000000 : ℝ) (992213284633/1000000000000 : ℝ) (3905304341/7812500000 : ℝ) (62484869457/125000000000 : ℝ) (158274040377/200000000000 : ℝ) (395685100951/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0210_exp_lower
  have heNumeric : (32107881533/15625000000 : ℝ)/4 ≤ Real.exp (-2664260104483/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107881533/15625000000 : ℝ)/4 ≤ Real.exp ((2053/16384 : ℝ)-(395685100951/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2053/16384 : ℝ) (8213/65536 : ℝ) (395685100951/500000000000 : ℝ) (32107881533/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0211; no trusted numerical premise.
theorem cover8_leaf0211_exp_radius : (998043546147014869/1000000000000000000 : ℝ) ≤ Real.exp ((-4107/262144 : ℝ)/8) ∧ Real.exp ((-4107/262144 : ℝ)/8) ≤ (99804354614701487/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4107/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0211_exp_lower : (460056793545476067/500000000000000000 : ℝ) ≤ Real.exp ((-10657043498347/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657043498347/16000000000000 : ℝ)/8) ≤ (184022717418190427/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657043498347/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0211_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490402249/100000000000 : ℝ) ≤ 4*Real.exp (8213/65536 : ℝ)*Real.exp (-mu (radius 8 (4107/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205490402249/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4107/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0211_exp_radius
  have hrNumeric : (984455126757/1000000000000 : ℝ) ≤ Real.exp (-4107/262144 : ℝ) ∧ Real.exp (-4107/262144 : ℝ) ≤ (492227563379/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984455126757/1000000000000 : ℝ) ≤ (radius 8 (4107/32768 : ℝ)) ∧ (radius 8 (4107/32768 : ℝ)) ≤ (492227563379/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4107/32768 : ℝ)) (984455126757/1000000000000 : ℝ) (492227563379/500000000000 : ℝ) (175636281559/1000000000000 : ℝ) (35127256313/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4107/32768 : ℝ)) (984455126757/1000000000000 : ℝ) (492227563379/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984455126757/1000000000000 : ℝ) (492227563379/500000000000 : ℝ) (496113781689/500000000000 : ℝ) (992227563379/1000000000000 : ℝ) (992197120917/1000000000000 : ℝ) (992197120919/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 1 (496113781689/500000000000 : ℝ) (992227563379/1000000000000 : ℝ) (992197120917/1000000000000 : ℝ) (992197120919/1000000000000 : ℝ) (992212342147/1000000000000 : ℝ) (992212342149/1000000000000 : ℝ) (99221234203/100000000000 : ℝ) (992212342033/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 2 (992212342147/1000000000000 : ℝ) (992212342149/1000000000000 : ℝ) (99221234203/100000000000 : ℝ) (992212342033/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 3 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 4 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 5 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 6 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4107/32768 : ℝ)) 7 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4107/32768 : ℝ))) (175636281559/1000000000000 : ℝ) (35127256313/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175636281559/1000000000000 : ℝ) (35127256313/200000000000 : ℝ) (587818140779/1000000000000 : ℝ) (587818140783/1000000000000 : ℝ) (419089825167/1000000000000 : ℝ) (16763593007/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 1 (587818140779/1000000000000 : ℝ) (587818140783/1000000000000 : ℝ) (419089825167/1000000000000 : ℝ) (16763593007/40000000000 : ℝ) (503453982973/1000000000000 : ℝ) (503453982979/1000000000000 : ℝ) (124083792719/250000000000 : ℝ) (496335170883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 2 (503453982973/1000000000000 : ℝ) (503453982979/1000000000000 : ℝ) (124083792719/250000000000 : ℝ) (496335170883/1000000000000 : ℝ) (124973644231/250000000000 : ℝ) (499894576931/1000000000000 : ℝ) (6248523809/12500000000 : ℝ) (62485238091/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 3 (124973644231/250000000000 : ℝ) (499894576931/1000000000000 : ℝ) (6248523809/12500000000 : ℝ) (62485238091/125000000000 : ℝ) (249944120411/500000000000 : ℝ) (49988824083/100000000000 : ℝ) (499888240781/1000000000000 : ℝ) (49988824079/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 4 (249944120411/500000000000 : ℝ) (49988824083/100000000000 : ℝ) (499888240781/1000000000000 : ℝ) (49988824079/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 5 (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 6 (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4107/32768 : ℝ))) 7 (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4107/32768 : ℝ)) hmem 8 (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4107/32768 : ℝ))) hcmem 8 (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4107/32768 : ℝ)) (124026542761/125000000000 : ℝ) (992212342091/1000000000000 : ℝ) (499888240801/1000000000000 : ℝ) (49988824081/100000000000 : ℝ) (791385653199/1000000000000 : ℝ) (791385653217/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0211_exp_lower
  have heNumeric : (205490402249/100000000000 : ℝ)/4 ≤ Real.exp (-10657043498347/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490402249/100000000000 : ℝ)/4 ≤ Real.exp ((8213/65536 : ℝ)-(791385653217/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8213/65536 : ℝ) (4107/32768 : ℝ) (791385653217/1000000000000 : ℝ) (205490402249/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0212; no trusted numerical premise.
theorem cover8_leaf0212_exp_radius : (998043308194919081/1000000000000000000 : ℝ) ≤ Real.exp ((-8215/524288 : ℝ)/8) ∧ Real.exp ((-8215/524288 : ℝ)/8) ≤ (499021654097459541/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8215/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0212_exp_lower : (4600567825474771/5000000000000000 : ℝ) ≤ Real.exp ((-5328523279141/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328523279141/8000000000000 : ℝ)/8) ≤ (920113565094954201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328523279141/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0212_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451814749/500000000000 : ℝ) ≤ 4*Real.exp (4107/32768 : ℝ)*Real.exp (-mu (radius 8 (8215/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451814749/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8215/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0212_exp_radius
  have hrNumeric : (49222662453/50000000000 : ℝ) ≤ Real.exp (-8215/524288 : ℝ) ∧ Real.exp (-8215/524288 : ℝ) ≤ (984453249061/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49222662453/50000000000 : ℝ) ≤ (radius 8 (8215/65536 : ℝ)) ∧ (radius 8 (8215/65536 : ℝ)) ≤ (984453249061/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8215/65536 : ℝ)) (49222662453/50000000000 : ℝ) (984453249061/1000000000000 : ℝ) (10977925367/62500000000 : ℝ) (175646805879/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8215/65536 : ℝ)) (49222662453/50000000000 : ℝ) (984453249061/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49222662453/50000000000 : ℝ) (984453249061/1000000000000 : ℝ) (99222662453/100000000000 : ℝ) (992226624531/1000000000000 : ℝ) (198439234937/200000000000 : ℝ) (496098087343/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 1 (99222662453/100000000000 : ℝ) (992226624531/1000000000000 : ℝ) (198439234937/200000000000 : ℝ) (496098087343/500000000000 : ℝ) (992211399607/1000000000000 : ℝ) (992211399609/1000000000000 : ℝ) (99221139949/100000000000 : ℝ) (248052849873/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 2 (992211399607/1000000000000 : ℝ) (992211399609/1000000000000 : ℝ) (99221139949/100000000000 : ℝ) (248052849873/250000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 3 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 4 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 5 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 6 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8215/65536 : ℝ)) 7 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8215/65536 : ℝ))) (10977925367/62500000000 : ℝ) (175646805879/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10977925367/62500000000 : ℝ) (175646805879/1000000000000 : ℝ) (73477925367/125000000000 : ℝ) (29391170147/50000000000 : ℝ) (419102381133/1000000000000 : ℝ) (419102381143/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 1 (73477925367/125000000000 : ℝ) (29391170147/50000000000 : ℝ) (419102381133/1000000000000 : ℝ) (419102381143/1000000000000 : ℝ) (251731446017/500000000000 : ℝ) (251731446021/500000000000 : ℝ) (49634482757/100000000000 : ℝ) (496344827579/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 2 (251731446017/500000000000 : ℝ) (251731446021/500000000000 : ℝ) (49634482757/100000000000 : ℝ) (496344827579/1000000000000 : ℝ) (249951929901/500000000000 : ℝ) (499903859811/1000000000000 : ℝ) (99978238099/200000000000 : ℝ) (62486398813/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 3 (249951929901/500000000000 : ℝ) (499903859811/1000000000000 : ℝ) (99978238099/200000000000 : ℝ) (62486398813/125000000000 : ℝ) (124974381287/250000000000 : ℝ) (249948762579/500000000000 : ℝ) (124974381277/250000000000 : ℝ) (249948762559/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 4 (124974381287/250000000000 : ℝ) (249948762579/500000000000 : ℝ) (124974381277/250000000000 : ℝ) (249948762559/500000000000 : ℝ) (62487190641/125000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 5 (62487190641/125000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 6 (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8215/65536 : ℝ))) 7 (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8215/65536 : ℝ)) hmem 8 (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8215/65536 : ℝ))) hcmem 8 (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8215/65536 : ℝ)) (248052849887/250000000000 : ℝ) (992211399551/1000000000000 : ℝ) (499897525127/1000000000000 : ℝ) (249948762569/500000000000 : ℝ) (791401103231/1000000000000 : ℝ) (197850275813/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0212_exp_lower
  have heNumeric : (1027451814749/500000000000 : ℝ)/4 ≤ Real.exp (-5328523279141/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451814749/500000000000 : ℝ)/4 ≤ Real.exp ((4107/32768 : ℝ)-(197850275813/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4107/32768 : ℝ) (8215/65536 : ℝ) (197850275813/250000000000 : ℝ) (1027451814749/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0213; no trusted numerical premise.
theorem cover8_leaf0213_exp_radius : (499021535121440013/500000000000000000 : ℝ) ≤ Real.exp ((-1027/65536 : ℝ)/8) ∧ Real.exp ((-1027/65536 : ℝ)/8) ≤ (998043070242880027/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1027/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0213_exp_lower : (920113543245714903/1000000000000000000 : ℝ) ≤ Real.exp ((-10657049597801/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657049597801/16000000000000 : ℝ)/8) ≤ (115014192905714363/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657049597801/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0213_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862904891/125000000000 : ℝ) ≤ 4*Real.exp (8215/65536 : ℝ)*Real.exp (-mu (radius 8 (1027/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256862904891/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1027/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0213_exp_radius
  have hrNumeric : (492225685683/500000000000 : ℝ) ≤ Real.exp (-1027/65536 : ℝ) ∧ Real.exp (-1027/65536 : ℝ) ≤ (984451371367/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492225685683/500000000000 : ℝ) ≤ (radius 8 (1027/8192 : ℝ)) ∧ (radius 8 (1027/8192 : ℝ)) ≤ (984451371367/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1027/8192 : ℝ)) (492225685683/500000000000 : ℝ) (984451371367/1000000000000 : ℝ) (87828664759/500000000000 : ℝ) (7026293181/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1027/8192 : ℝ)) (492225685683/500000000000 : ℝ) (984451371367/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492225685683/500000000000 : ℝ) (984451371367/1000000000000 : ℝ) (992225685683/1000000000000 : ℝ) (248056421421/250000000000 : ℝ) (992195228453/1000000000000 : ℝ) (198439045691/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 1 (992225685683/1000000000000 : ℝ) (248056421421/250000000000 : ℝ) (992195228453/1000000000000 : ℝ) (198439045691/200000000000 : ℝ) (248052614267/250000000000 : ℝ) (99221045707/100000000000 : ℝ) (992210456951/1000000000000 : ℝ) (992210456953/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 2 (248052614267/250000000000 : ℝ) (99221045707/100000000000 : ℝ) (992210456951/1000000000000 : ℝ) (992210456953/1000000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 3 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 4 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 5 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 6 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1027/8192 : ℝ)) 7 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1027/8192 : ℝ))) (87828664759/500000000000 : ℝ) (7026293181/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87828664759/500000000000 : ℝ) (7026293181/40000000000 : ℝ) (587828664759/1000000000000 : ℝ) (587828664763/1000000000000 : ℝ) (52389366991/125000000000 : ℝ) (419114935937/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 1 (587828664759/1000000000000 : ℝ) (587828664763/1000000000000 : ℝ) (52389366991/125000000000 : ℝ) (419114935937/1000000000000 : ℝ) (503471800343/1000000000000 : ℝ) (10069436007/20000000000 : ℝ) (3970835867/8000000000 : ℝ) (496354483383/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 2 (503471800343/1000000000000 : ℝ) (10069436007/20000000000 : ℝ) (3970835867/8000000000 : ℝ) (496354483383/1000000000000 : ℝ) (499913141859/1000000000000 : ℝ) (499913141867/1000000000000 : ℝ) (499900475447/1000000000000 : ℝ) (7810944929/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 3 (499913141859/1000000000000 : ℝ) (499913141867/1000000000000 : ℝ) (499900475447/1000000000000 : ℝ) (7810944929/15625000000 : ℝ) (499906808653/1000000000000 : ℝ) (249953404331/500000000000 : ℝ) (124976702153/250000000000 : ℝ) (249953404311/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 4 (499906808653/1000000000000 : ℝ) (249953404331/500000000000 : ℝ) (124976702153/250000000000 : ℝ) (249953404311/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 5 (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 6 (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1027/8192 : ℝ))) 7 (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1027/8192 : ℝ)) hmem 8 (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1027/8192 : ℝ))) hcmem 8 (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1027/8192 : ℝ)) (992210457009/1000000000000 : ℝ) (248052614253/250000000000 : ℝ) (62488351079/125000000000 : ℝ) (249953404321/500000000000 : ℝ) (98927068999/125000000000 : ℝ) (791416552011/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0213_exp_lower
  have heNumeric : (256862904891/125000000000 : ℝ)/4 ≤ Real.exp (-10657049597801/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862904891/125000000000 : ℝ)/4 ≤ Real.exp ((8215/65536 : ℝ)-(791416552011/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8215/65536 : ℝ) (1027/8192 : ℝ) (791416552011/1000000000000 : ℝ) (256862904891/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0214; no trusted numerical premise.
theorem cover8_leaf0214_exp_radius : (998042832290897703/1000000000000000000 : ℝ) ≤ Real.exp ((-8217/524288 : ℝ)/8) ∧ Real.exp ((-8217/524288 : ℝ)/8) ≤ (124755354036362213/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8217/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0214_exp_lower : (460056760771904651/500000000000000000 : ℝ) ≤ Real.exp ((-1332131577103/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332131577103/2000000000000 : ℝ)/8) ≤ (920113521543809303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332131577103/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0214_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490285139/100000000000 : ℝ) ≤ 4*Real.exp (1027/8192 : ℝ)*Real.exp (-mu (radius 8 (8217/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205490285139/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8217/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0214_exp_radius
  have hrNumeric : (246112373419/250000000000 : ℝ) ≤ Real.exp (-8217/524288 : ℝ) ∧ Real.exp (-8217/524288 : ℝ) ≤ (984449493677/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246112373419/250000000000 : ℝ) ≤ (radius 8 (8217/65536 : ℝ)) ∧ (radius 8 (8217/65536 : ℝ)) ≤ (984449493677/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8217/65536 : ℝ)) (246112373419/250000000000 : ℝ) (984449493677/1000000000000 : ℝ) (175667852491/1000000000000 : ℝ) (87833926249/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8217/65536 : ℝ)) (246112373419/250000000000 : ℝ) (984449493677/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246112373419/250000000000 : ℝ) (984449493677/1000000000000 : ℝ) (496112373419/500000000000 : ℝ) (992224746839/1000000000000 : ℝ) (496097141111/500000000000 : ℝ) (62012142639/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 1 (496112373419/500000000000 : ℝ) (992224746839/1000000000000 : ℝ) (496097141111/500000000000 : ℝ) (62012142639/62500000000 : ℝ) (99220951453/100000000000 : ℝ) (248052378633/250000000000 : ℝ) (992209514413/1000000000000 : ℝ) (198441902883/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 2 (99220951453/100000000000 : ℝ) (248052378633/250000000000 : ℝ) (992209514413/1000000000000 : ℝ) (198441902883/200000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 3 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 4 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 5 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 6 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8217/65536 : ℝ)) 7 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8217/65536 : ℝ))) (175667852491/1000000000000 : ℝ) (87833926249/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175667852491/1000000000000 : ℝ) (87833926249/500000000000 : ℝ) (117566785249/200000000000 : ℝ) (587833926249/1000000000000 : ℝ) (419127489543/1000000000000 : ℝ) (26195468097/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 1 (117566785249/200000000000 : ℝ) (587833926249/1000000000000 : ℝ) (419127489543/1000000000000 : ℝ) (26195468097/62500000000 : ℝ) (251740353947/500000000000 : ℝ) (503480707901/1000000000000 : ℝ) (124091034571/250000000000 : ℝ) (124091034573/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 2 (251740353947/500000000000 : ℝ) (503480707901/1000000000000 : ℝ) (124091034571/250000000000 : ℝ) (124091034573/250000000000 : ℝ) (499922423089/1000000000000 : ℝ) (499922423097/1000000000000 : ℝ) (499909759573/1000000000000 : ℝ) (499909759581/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 3 (499922423089/1000000000000 : ℝ) (499922423097/1000000000000 : ℝ) (499909759573/1000000000000 : ℝ) (499909759581/1000000000000 : ℝ) (499916091331/1000000000000 : ℝ) (499916091339/1000000000000 : ℝ) (49991609129/100000000000 : ℝ) (499916091299/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 4 (499916091331/1000000000000 : ℝ) (499916091339/1000000000000 : ℝ) (49991609129/100000000000 : ℝ) (499916091299/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 5 (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 6 (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8217/65536 : ℝ))) 7 (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8217/65536 : ℝ)) hmem 8 (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8217/65536 : ℝ))) hcmem 8 (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8217/65536 : ℝ)) (992209514471/1000000000000 : ℝ) (496104757237/500000000000 : ℝ) (49991609131/100000000000 : ℝ) (499916091319/1000000000000 : ℝ) (49464499967/62500000000 : ℝ) (791431999489/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0214_exp_lower
  have heNumeric : (205490285139/100000000000 : ℝ)/4 ≤ Real.exp (-1332131577103/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490285139/100000000000 : ℝ)/4 ≤ Real.exp ((1027/8192 : ℝ)-(791431999489/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1027/8192 : ℝ) (8217/65536 : ℝ) (791431999489/1000000000000 : ℝ) (205490285139/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0215; no trusted numerical premise.
theorem cover8_leaf0215_exp_radius : (998042594338972111/1000000000000000000 : ℝ) ≤ Real.exp ((-4109/262144 : ℝ)/8) ∧ Real.exp ((-4109/262144 : ℝ)/8) ≤ (62377662146185757/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4109/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0215_exp_lower : (920113499987857217/1000000000000000000 : ℝ) ≤ Real.exp ((-10657055615543/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657055615543/16000000000000 : ℝ)/8) ≤ (460056749993928609/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657055615543/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0215_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902466261/1000000000000 : ℝ) ≤ 4*Real.exp (8217/65536 : ℝ)*Real.exp (-mu (radius 8 (4109/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902466261/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4109/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0215_exp_radius
  have hrNumeric : (984447615989/1000000000000 : ℝ) ≤ Real.exp (-4109/262144 : ℝ) ∧ Real.exp (-4109/262144 : ℝ) ≤ (98444761599/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984447615989/1000000000000 : ℝ) ≤ (radius 8 (4109/32768 : ℝ)) ∧ (radius 8 (4109/32768 : ℝ)) ≤ (98444761599/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4109/32768 : ℝ)) (984447615989/1000000000000 : ℝ) (98444761599/100000000000 : ℝ) (175678374797/1000000000000 : ℝ) (43919593701/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4109/32768 : ℝ)) (984447615989/1000000000000 : ℝ) (98444761599/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984447615989/1000000000000 : ℝ) (98444761599/100000000000 : ℝ) (496111903997/500000000000 : ℝ) (198444761599/200000000000 : ℝ) (992193335993/1000000000000 : ℝ) (496096667997/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 1 (496111903997/500000000000 : ℝ) (198444761599/200000000000 : ℝ) (992193335993/1000000000000 : ℝ) (496096667997/500000000000 : ℝ) (992208571993/1000000000000 : ℝ) (198441714399/200000000000 : ℝ) (248052142969/250000000000 : ℝ) (496104285939/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 2 (992208571993/1000000000000 : ℝ) (198441714399/200000000000 : ℝ) (248052142969/250000000000 : ℝ) (496104285939/500000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 3 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 4 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 5 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 6 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4109/32768 : ℝ)) 7 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4109/32768 : ℝ))) (175678374797/1000000000000 : ℝ) (43919593701/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175678374797/1000000000000 : ℝ) (43919593701/250000000000 : ℝ) (293919593699/500000000000 : ℝ) (293919593701/500000000000 : ℝ) (419140041987/1000000000000 : ℝ) (104785010499/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 1 (293919593699/500000000000 : ℝ) (293919593701/500000000000 : ℝ) (419140041987/1000000000000 : ℝ) (104785010499/250000000000 : ℝ) (125872403673/250000000000 : ℝ) (503489614699/1000000000000 : ℝ) (99274758461/200000000000 : ℝ) (496373792313/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 2 (125872403673/250000000000 : ℝ) (503489614699/1000000000000 : ℝ) (99274758461/200000000000 : ℝ) (496373792313/1000000000000 : ℝ) (249965851749/500000000000 : ℝ) (249965851753/500000000000 : ℝ) (124979760719/250000000000 : ℝ) (99983808577/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 3 (249965851749/500000000000 : ℝ) (249965851753/500000000000 : ℝ) (124979760719/250000000000 : ℝ) (99983808577/200000000000 : ℝ) (499925373187/1000000000000 : ℝ) (124981343299/250000000000 : ℝ) (249962686573/500000000000 : ℝ) (124981343289/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 4 (499925373187/1000000000000 : ℝ) (124981343299/250000000000 : ℝ) (249962686573/500000000000 : ℝ) (124981343289/250000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 5 (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 6 (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4109/32768 : ℝ))) 7 (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4109/32768 : ℝ)) hmem 8 (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4109/32768 : ℝ))) hcmem 8 (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4109/32768 : ℝ)) (496104285967/500000000000 : ℝ) (992208571937/1000000000000 : ℝ) (249962686583/500000000000 : ℝ) (62490671647/125000000000 : ℝ) (791447445679/1000000000000 : ℝ) (395723722849/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0215_exp_lower
  have heNumeric : (2054902466261/1000000000000 : ℝ)/4 ≤ Real.exp (-10657055615543/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902466261/1000000000000 : ℝ)/4 ≤ Real.exp ((8217/65536 : ℝ)-(395723722849/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8217/65536 : ℝ) (4109/32768 : ℝ) (395723722849/500000000000 : ℝ) (2054902466261/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0216; no trusted numerical premise.
theorem cover8_leaf0216_exp_radius : (249510589096775813/250000000000000000 : ℝ) ≤ Real.exp ((-8219/524288 : ℝ)/8) ∧ Real.exp ((-8219/524288 : ℝ)/8) ≤ (998042356387103253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8219/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0216_exp_lower : (460056739289676911/500000000000000000 : ℝ) ≤ Real.exp ((-2728207/4096000 : ℝ)/8) ∧ Real.exp ((-2728207/4096000 : ℝ)/8) ≤ (920113478579353823/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2728207/4096000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0216_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980416753/200000000000 : ℝ) ≤ 4*Real.exp (4109/32768 : ℝ)*Real.exp (-mu (radius 8 (8219/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980416753/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8219/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0216_exp_radius
  have hrNumeric : (492222869153/500000000000 : ℝ) ≤ Real.exp (-8219/524288 : ℝ) ∧ Real.exp (-8219/524288 : ℝ) ≤ (984445738307/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492222869153/500000000000 : ℝ) ≤ (radius 8 (8219/65536 : ℝ)) ∧ (radius 8 (8219/65536 : ℝ)) ≤ (984445738307/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8219/65536 : ℝ)) (492222869153/500000000000 : ℝ) (984445738307/1000000000000 : ℝ) (175688896431/1000000000000 : ℝ) (175688896437/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8219/65536 : ℝ)) (492222869153/500000000000 : ℝ) (984445738307/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492222869153/500000000000 : ℝ) (984445738307/1000000000000 : ℝ) (992222869153/1000000000000 : ℝ) (496111434577/500000000000 : ℝ) (248048097441/250000000000 : ℝ) (198438477953/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 1 (992222869153/1000000000000 : ℝ) (496111434577/500000000000 : ℝ) (248048097441/250000000000 : ℝ) (198438477953/200000000000 : ℝ) (496103814729/500000000000 : ℝ) (49610381473/50000000000 : ℝ) (992207629341/1000000000000 : ℝ) (992207629343/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 2 (496103814729/500000000000 : ℝ) (49610381473/50000000000 : ℝ) (992207629341/1000000000000 : ℝ) (992207629343/1000000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 3 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 4 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 5 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 6 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8219/65536 : ℝ)) 7 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8219/65536 : ℝ))) (175688896431/1000000000000 : ℝ) (175688896437/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175688896431/1000000000000 : ℝ) (175688896437/1000000000000 : ℝ) (117568889643/200000000000 : ℝ) (587844448219/1000000000000 : ℝ) (419152593253/1000000000000 : ℝ) (419152593261/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 1 (117568889643/200000000000 : ℝ) (587844448219/1000000000000 : ℝ) (419152593253/1000000000000 : ℝ) (419152593261/1000000000000 : ℝ) (251749260367/500000000000 : ℝ) (25174926037/50000000000 : ℝ) (496383445431/1000000000000 : ℝ) (496383445439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 2 (251749260367/500000000000 : ℝ) (25174926037/50000000000 : ℝ) (496383445431/1000000000000 : ℝ) (496383445439/1000000000000 : ℝ) (249970491541/500000000000 : ℝ) (49994098309/100000000000 : ℝ) (249964162677/500000000000 : ℝ) (249964162681/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 3 (249970491541/500000000000 : ℝ) (49994098309/100000000000 : ℝ) (249964162677/500000000000 : ℝ) (249964162681/500000000000 : ℝ) (249967327109/500000000000 : ℝ) (249967327113/500000000000 : ℝ) (499934654177/1000000000000 : ℝ) (249967327093/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 4 (249967327109/500000000000 : ℝ) (249967327113/500000000000 : ℝ) (499934654177/1000000000000 : ℝ) (249967327093/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 5 (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 6 (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8219/65536 : ℝ))) 7 (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8219/65536 : ℝ)) hmem 8 (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8219/65536 : ℝ))) hcmem 8 (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8219/65536 : ℝ)) (992207629399/1000000000000 : ℝ) (496103814701/500000000000 : ℝ) (499934654197/1000000000000 : ℝ) (249967327103/500000000000 : ℝ) (49466430663/62500000000 : ℝ) (405229/512000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0216_exp_lower
  have heNumeric : (410980416753/200000000000 : ℝ)/4 ≤ Real.exp (-2728207/4096000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980416753/200000000000 : ℝ)/4 ≤ Real.exp ((4109/32768 : ℝ)-(405229/512000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4109/32768 : ℝ) (8219/65536 : ℝ) (405229/512000 : ℝ) (410980416753/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0217; no trusted numerical premise.
theorem cover8_leaf0217_exp_radius : (7984336947482329/8000000000000000 : ℝ) ≤ Real.exp ((-2055/131072 : ℝ)/8) ∧ Real.exp ((-2055/131072 : ℝ)/8) ≤ (499021059217645563/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2055/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0217_exp_lower : (18402269146356781/20000000000000000 : ℝ) ≤ Real.exp ((-10657061551509/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061551509/16000000000000 : ℝ)/8) ≤ (920113457317839051/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061551509/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0217_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862712987/125000000000 : ℝ) ≤ 4*Real.exp (8219/65536 : ℝ)*Real.exp (-mu (radius 8 (2055/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (256862712987/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2055/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0217_exp_radius
  have hrNumeric : (984443860627/1000000000000 : ℝ) ≤ Real.exp (-2055/131072 : ℝ) ∧ Real.exp (-2055/131072 : ℝ) ≤ (246110965157/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984443860627/1000000000000 : ℝ) ≤ (radius 8 (2055/16384 : ℝ)) ∧ (radius 8 (2055/16384 : ℝ)) ≤ (246110965157/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2055/16384 : ℝ)) (984443860627/1000000000000 : ℝ) (246110965157/250000000000 : ℝ) (175699417391/1000000000000 : ℝ) (87849708699/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2055/16384 : ℝ)) (984443860627/1000000000000 : ℝ) (246110965157/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984443860627/1000000000000 : ℝ) (246110965157/250000000000 : ℝ) (992221930313/1000000000000 : ℝ) (496110965157/500000000000 : ℝ) (62011965221/62500000000 : ℝ) (992191443537/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 1 (992221930313/1000000000000 : ℝ) (496110965157/500000000000 : ℝ) (62011965221/62500000000 : ℝ) (992191443537/1000000000000 : ℝ) (248051671731/250000000000 : ℝ) (496103343463/500000000000 : ℝ) (992206686807/1000000000000 : ℝ) (992206686809/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 2 (248051671731/250000000000 : ℝ) (496103343463/500000000000 : ℝ) (992206686807/1000000000000 : ℝ) (992206686809/1000000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 3 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 4 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 5 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 6 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2055/16384 : ℝ)) 7 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2055/16384 : ℝ))) (175699417391/1000000000000 : ℝ) (87849708699/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175699417391/1000000000000 : ℝ) (87849708699/500000000000 : ℝ) (117569941739/200000000000 : ℝ) (587849708699/1000000000000 : ℝ) (419165143339/1000000000000 : ℝ) (419165143349/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 1 (117569941739/200000000000 : ℝ) (587849708699/1000000000000 : ℝ) (419165143339/1000000000000 : ℝ) (419165143349/1000000000000 : ℝ) (503507426017/1000000000000 : ℝ) (62938428253/125000000000 : ℝ) (248196548831/500000000000 : ℝ) (496393097671/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 2 (503507426017/1000000000000 : ℝ) (62938428253/125000000000 : ℝ) (248196548831/500000000000 : ℝ) (496393097671/1000000000000 : ℝ) (499950261839/1000000000000 : ℝ) (62493782731/125000000000 : ℝ) (499937607003/1000000000000 : ℝ) (124984401753/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 3 (499950261839/1000000000000 : ℝ) (62493782731/125000000000 : ℝ) (499937607003/1000000000000 : ℝ) (124984401753/250000000000 : ℝ) (499943934421/1000000000000 : ℝ) (49994393443/100000000000 : ℝ) (24997196719/50000000000 : ℝ) (49994393439/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 4 (499943934421/1000000000000 : ℝ) (49994393443/100000000000 : ℝ) (24997196719/50000000000 : ℝ) (49994393439/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 5 (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 6 (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2055/16384 : ℝ))) 7 (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2055/16384 : ℝ)) hmem 8 (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2055/16384 : ℝ))) hcmem 8 (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2055/16384 : ℝ)) (198441337373/200000000000 : ℝ) (248051671717/250000000000 : ℝ) (312464959/625000000 : ℝ) (49994393441/100000000000 : ℝ) (395739167127/500000000000 : ℝ) (395739167137/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0217_exp_lower
  have heNumeric : (256862712987/125000000000 : ℝ)/4 ≤ Real.exp (-10657061551509/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862712987/125000000000 : ℝ)/4 ≤ Real.exp ((8219/65536 : ℝ)-(395739167137/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8219/65536 : ℝ) (2055/16384 : ℝ) (395739167137/500000000000 : ℝ) (256862712987/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0218; no trusted numerical premise.
theorem cover8_leaf0218_exp_radius : (998041880483535731/1000000000000000000 : ℝ) ≤ Real.exp ((-8221/524288 : ℝ)/8) ∧ Real.exp ((-8221/524288 : ℝ)/8) ≤ (249510470120883933/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8221/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0218_exp_lower : (184022687240524561/200000000000000000 : ℝ) ≤ Real.exp ((-2664266122229/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664266122229/4000000000000 : ℝ)/8) ≤ (460056718101311403/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664266122229/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0218_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901326641/1000000000000 : ℝ) ≤ 4*Real.exp (2055/16384 : ℝ)*Real.exp (-mu (radius 8 (8221/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901326641/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8221/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0218_exp_radius
  have hrNumeric : (984441982951/1000000000000 : ℝ) ≤ Real.exp (-8221/524288 : ℝ) ∧ Real.exp (-8221/524288 : ℝ) ≤ (123055247869/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984441982951/1000000000000 : ℝ) ≤ (radius 8 (8221/65536 : ℝ)) ∧ (radius 8 (8221/65536 : ℝ)) ≤ (123055247869/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8221/65536 : ℝ)) (984441982951/1000000000000 : ℝ) (123055247869/125000000000 : ℝ) (35141987537/200000000000 : ℝ) (43927484423/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8221/65536 : ℝ)) (984441982951/1000000000000 : ℝ) (123055247869/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984441982951/1000000000000 : ℝ) (123055247869/125000000000 : ℝ) (39688839659/40000000000 : ℝ) (248055247869/250000000000 : ℝ) (992190497309/1000000000000 : ℝ) (99219049731/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 1 (39688839659/40000000000 : ℝ) (248055247869/250000000000 : ℝ) (992190497309/1000000000000 : ℝ) (99219049731/100000000000 : ℝ) (124025718049/125000000000 : ℝ) (992205744393/1000000000000 : ℝ) (496102872137/500000000000 : ℝ) (248051436069/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 2 (124025718049/125000000000 : ℝ) (992205744393/1000000000000 : ℝ) (496102872137/500000000000 : ℝ) (248051436069/250000000000 : ℝ) (992205744333/1000000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 3 (992205744333/1000000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 4 (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 5 (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 6 (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8221/65536 : ℝ)) 7 (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8221/65536 : ℝ))) (35141987537/200000000000 : ℝ) (43927484423/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35141987537/200000000000 : ℝ) (43927484423/250000000000 : ℝ) (293927484421/500000000000 : ℝ) (293927484423/500000000000 : ℝ) (83835538451/200000000000 : ℝ) (83835538453/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 1 (293927484421/500000000000 : ℝ) (293927484423/500000000000 : ℝ) (83835538451/200000000000 : ℝ) (83835538453/200000000000 : ℝ) (125879082637/250000000000 : ℝ) (125879082639/250000000000 : ℝ) (99280549801/200000000000 : ℝ) (496402749013/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 2 (125879082637/250000000000 : ℝ) (125879082639/250000000000 : ℝ) (99280549801/200000000000 : ℝ) (496402749013/1000000000000 : ℝ) (7811867809/15625000000 : ℝ) (99991907957/200000000000 : ℝ) (62493360979/125000000000 : ℝ) (499946887841/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 3 (7811867809/15625000000 : ℝ) (99991907957/200000000000 : ℝ) (62493360979/125000000000 : ℝ) (499946887841/1000000000000 : ℝ) (124988303451/250000000000 : ℝ) (499953213813/1000000000000 : ℝ) (499953213763/1000000000000 : ℝ) (499953213773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 4 (124988303451/250000000000 : ℝ) (499953213813/1000000000000 : ℝ) (499953213763/1000000000000 : ℝ) (499953213773/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 5 (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 6 (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8221/65536 : ℝ))) 7 (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8221/65536 : ℝ)) hmem 8 (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8221/65536 : ℝ))) hcmem 8 (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8221/65536 : ℝ)) (248051436083/250000000000 : ℝ) (198441148867/200000000000 : ℝ) (499953213783/1000000000000 : ℝ) (499953213793/1000000000000 : ℝ) (791493776631/1000000000000 : ℝ) (791493776651/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0218_exp_lower
  have heNumeric : (2054901326641/1000000000000 : ℝ)/4 ≤ Real.exp (-2664266122229/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901326641/1000000000000 : ℝ)/4 ≤ Real.exp ((2055/16384 : ℝ)-(791493776651/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2055/16384 : ℝ) (8221/65536 : ℝ) (791493776651/1000000000000 : ℝ) (2054901326641/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0219; no trusted numerical premise.
theorem cover8_leaf0219_exp_radius : (249510410632959267/250000000000000000 : ℝ) ≤ Real.exp ((-4111/262144 : ℝ)/8) ∧ Real.exp ((-4111/262144 : ℝ)/8) ≤ (998041642531837069/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4111/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0219_exp_lower : (920113415234625191/1000000000000000000 : ℝ) ≤ Real.exp ((-10657067405843/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657067405843/16000000000000 : ℝ)/8) ≤ (115014176904328149/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657067405843/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0219_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431309501/62500000000 : ℝ) ≤ 4*Real.exp (8221/65536 : ℝ)*Real.exp (-mu (radius 8 (4111/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (128431309501/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4111/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0219_exp_radius
  have hrNumeric : (984440105279/1000000000000 : ℝ) ≤ Real.exp (-4111/262144 : ℝ) ∧ Real.exp (-4111/262144 : ℝ) ≤ (3076375329/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984440105279/1000000000000 : ℝ) ≤ (radius 8 (4111/32768 : ℝ)) ∧ (radius 8 (4111/32768 : ℝ)) ≤ (3076375329/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4111/32768 : ℝ)) (984440105279/1000000000000 : ℝ) (3076375329/3125000000 : ℝ) (175720457307/1000000000000 : ℝ) (175720457313/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4111/32768 : ℝ)) (984440105279/1000000000000 : ℝ) (3076375329/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984440105279/1000000000000 : ℝ) (3076375329/3125000000 : ℝ) (992220052639/1000000000000 : ℝ) (6201375329/6250000000 : ℝ) (992189551083/1000000000000 : ℝ) (248047387771/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 1 (992220052639/1000000000000 : ℝ) (6201375329/6250000000 : ℝ) (992189551083/1000000000000 : ℝ) (248047387771/250000000000 : ℝ) (992204801861/1000000000000 : ℝ) (496102400931/500000000000 : ℝ) (992204801743/1000000000000 : ℝ) (198440960349/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 2 (992204801861/1000000000000 : ℝ) (496102400931/500000000000 : ℝ) (992204801743/1000000000000 : ℝ) (198440960349/200000000000 : ℝ) (496102400901/500000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 3 (496102400901/500000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 4 (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 5 (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 6 (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4111/32768 : ℝ)) 7 (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4111/32768 : ℝ))) (175720457307/1000000000000 : ℝ) (175720457313/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175720457307/1000000000000 : ℝ) (175720457313/1000000000000 : ℝ) (587860228653/1000000000000 : ℝ) (587860228657/1000000000000 : ℝ) (209595119997/500000000000 : ℝ) (419190240003/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 1 (587860228653/1000000000000 : ℝ) (587860228657/1000000000000 : ℝ) (209595119997/500000000000 : ℝ) (419190240003/1000000000000 : ℝ) (503525234323/1000000000000 : ℝ) (50352523433/100000000000 : ℝ) (248206199727/500000000000 : ℝ) (248206199731/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 2 (503525234323/1000000000000 : ℝ) (50352523433/100000000000 : ℝ) (248206199727/500000000000 : ℝ) (248206199731/500000000000 : ℝ) (62496102111/125000000000 : ℝ) (1953003191/3906250000 : ℝ) (249978083917/500000000000 : ℝ) (499956167843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 3 (62496102111/125000000000 : ℝ) (1953003191/3906250000 : ℝ) (249978083917/500000000000 : ℝ) (499956167843/1000000000000 : ℝ) (499962492361/1000000000000 : ℝ) (49996249237/100000000000 : ℝ) (3124765577/6250000000 : ℝ) (49996249233/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 4 (499962492361/1000000000000 : ℝ) (49996249237/100000000000 : ℝ) (3124765577/6250000000 : ℝ) (49996249233/100000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 5 (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 6 (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4111/32768 : ℝ))) 7 (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4111/32768 : ℝ)) hmem 8 (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4111/32768 : ℝ))) hcmem 8 (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4111/32768 : ℝ)) (992204801801/1000000000000 : ℝ) (248051200451/250000000000 : ℝ) (24998124617/50000000000 : ℝ) (9999249847/20000000000 : ℝ) (791509217729/1000000000000 : ℝ) (197877304437/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0219_exp_lower
  have heNumeric : (128431309501/62500000000 : ℝ)/4 ≤ Real.exp (-10657067405843/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431309501/62500000000 : ℝ)/4 ≤ Real.exp ((8221/65536 : ℝ)-(197877304437/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8221/65536 : ℝ) (4111/32768 : ℝ) (197877304437/250000000000 : ℝ) (128431309501/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0220; no trusted numerical premise.
theorem cover8_leaf0220_exp_radius : (998041404580195137/1000000000000000000 : ℝ) ≤ Real.exp ((-8223/524288 : ℝ)/8) ∧ Real.exp ((-8223/524288 : ℝ)/8) ≤ (499020702290097569/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8223/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0220_exp_lower : (920113394412811071/1000000000000000000 : ℝ) ≤ Real.exp ((-5328535151217/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328535151217/8000000000000 : ℝ)/8) ≤ (14376771787700173/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328535151217/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0220_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900580003/1000000000000 : ℝ) ≤ 4*Real.exp (4111/32768 : ℝ)*Real.exp (-mu (radius 8 (8223/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900580003/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8223/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0220_exp_radius
  have hrNumeric : (98443822761/100000000000 : ℝ) ≤ Real.exp (-8223/524288 : ℝ) ∧ Real.exp (-8223/524288 : ℝ) ≤ (984438227611/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98443822761/100000000000 : ℝ) ≤ (radius 8 (8223/65536 : ℝ)) ∧ (radius 8 (8223/65536 : ℝ)) ≤ (984438227611/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8223/65536 : ℝ)) (98443822761/100000000000 : ℝ) (984438227611/1000000000000 : ℝ) (87865488131/500000000000 : ℝ) (43932744067/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8223/65536 : ℝ)) (98443822761/100000000000 : ℝ) (984438227611/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98443822761/100000000000 : ℝ) (984438227611/1000000000000 : ℝ) (198443822761/200000000000 : ℝ) (496109556903/500000000000 : ℝ) (992188604857/1000000000000 : ℝ) (992188604859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 1 (198443822761/200000000000 : ℝ) (496109556903/500000000000 : ℝ) (992188604857/1000000000000 : ℝ) (992188604859/1000000000000 : ℝ) (992203859331/1000000000000 : ℝ) (992203859333/1000000000000 : ℝ) (992203859213/1000000000000 : ℝ) (62012741201/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 2 (992203859331/1000000000000 : ℝ) (992203859333/1000000000000 : ℝ) (992203859213/1000000000000 : ℝ) (62012741201/62500000000 : ℝ) (124025482409/125000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 3 (124025482409/125000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 4 (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 5 (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 6 (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8223/65536 : ℝ)) 7 (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8223/65536 : ℝ))) (87865488131/500000000000 : ℝ) (43932744067/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87865488131/500000000000 : ℝ) (43932744067/250000000000 : ℝ) (587865488131/1000000000000 : ℝ) (293932744067/500000000000 : ℝ) (209601393281/500000000000 : ℝ) (41920278657/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 1 (587865488131/1000000000000 : ℝ) (293932744067/500000000000 : ℝ) (209601393281/500000000000 : ℝ) (41920278657/100000000000 : ℝ) (251767068673/500000000000 : ℝ) (62941767169/125000000000 : ℝ) (248211024507/500000000000 : ℝ) (496422049021/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 2 (251767068673/500000000000 : ℝ) (62941767169/125000000000 : ℝ) (248211024507/500000000000 : ℝ) (496422049021/1000000000000 : ℝ) (24998904659/50000000000 : ℝ) (499978093187/1000000000000 : ℝ) (99993089403/200000000000 : ℝ) (499965447023/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 3 (24998904659/50000000000 : ℝ) (499978093187/1000000000000 : ℝ) (99993089403/200000000000 : ℝ) (499965447023/1000000000000 : ℝ) (499971770097/1000000000000 : ℝ) (99994354021/200000000000 : ℝ) (499971770057/1000000000000 : ℝ) (249985885033/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 4 (499971770097/1000000000000 : ℝ) (99994354021/200000000000 : ℝ) (499971770057/1000000000000 : ℝ) (249985885033/500000000000 : ℝ) (499971770077/1000000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 5 (499971770077/1000000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 6 (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8223/65536 : ℝ))) 7 (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8223/65536 : ℝ)) hmem 8 (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8223/65536 : ℝ))) hcmem 8 (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8223/65536 : ℝ)) (992203859271/1000000000000 : ℝ) (39688154371/40000000000 : ℝ) (124992942519/250000000000 : ℝ) (249985885043/500000000000 : ℝ) (395762328777/500000000000 : ℝ) (395762328787/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0220_exp_lower
  have heNumeric : (2054900580003/1000000000000 : ℝ)/4 ≤ Real.exp (-5328535151217/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900580003/1000000000000 : ℝ)/4 ≤ Real.exp ((4111/32768 : ℝ)-(395762328787/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4111/32768 : ℝ) (8223/65536 : ℝ) (395762328787/500000000000 : ℝ) (2054900580003/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0221; no trusted numerical premise.
theorem cover8_leaf0221_exp_radius : (998041166628609939/1000000000000000000 : ℝ) ≤ Real.exp ((-257/16384 : ℝ)/8) ∧ Real.exp ((-257/16384 : ℝ)/8) ≤ (49902058331430497/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-257/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0221_exp_lower : (230028343434525137/250000000000000000 : ℝ) ≤ Real.exp ((-10657073178561/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657073178561/16000000000000 : ℝ)/8) ≤ (920113373738100549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657073178561/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0221_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900210619/1000000000000 : ℝ) ≤ 4*Real.exp (8223/65536 : ℝ)*Real.exp (-mu (radius 8 (257/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900210619/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (257/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0221_exp_radius
  have hrNumeric : (196887269989/200000000000 : ℝ) ≤ Real.exp (-257/16384 : ℝ) ∧ Real.exp (-257/16384 : ℝ) ≤ (492218174973/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196887269989/200000000000 : ℝ) ≤ (radius 8 (257/2048 : ℝ)) ∧ (radius 8 (257/2048 : ℝ)) ≤ (492218174973/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (257/2048 : ℝ)) (196887269989/200000000000 : ℝ) (492218174973/500000000000 : ℝ) (35148298909/200000000000 : ℝ) (175741494551/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (257/2048 : ℝ)) (196887269989/200000000000 : ℝ) (492218174973/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (257/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196887269989/200000000000 : ℝ) (492218174973/500000000000 : ℝ) (248054543743/250000000000 : ℝ) (992218174973/1000000000000 : ℝ) (992187658633/1000000000000 : ℝ) (198437531727/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (257/2048 : ℝ)) 1 (248054543743/250000000000 : ℝ) (992218174973/1000000000000 : ℝ) (992187658633/1000000000000 : ℝ) (198437531727/200000000000 : ℝ) (496101458401/500000000000 : ℝ) (248050729201/250000000000 : ℝ) (198440583337/200000000000 : ℝ) (992202916687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (257/2048 : ℝ)) 2 (496101458401/500000000000 : ℝ) (248050729201/250000000000 : ℝ) (198440583337/200000000000 : ℝ) (992202916687/1000000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (257/2048 : ℝ)) 3 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (257/2048 : ℝ)) 4 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (257/2048 : ℝ)) 5 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (257/2048 : ℝ)) 6 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (257/2048 : ℝ)) 7 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (257/2048 : ℝ))) (35148298909/200000000000 : ℝ) (175741494551/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35148298909/200000000000 : ℝ) (175741494551/1000000000000 : ℝ) (73483843409/125000000000 : ℝ) (146967686819/250000000000 : ℝ) (419215331953/1000000000000 : ℝ) (419215331961/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 1 (73483843409/125000000000 : ℝ) (146967686819/250000000000 : ℝ) (419215331953/1000000000000 : ℝ) (419215331961/1000000000000 : ℝ) (125885759903/250000000000 : ℝ) (503543039619/1000000000000 : ℝ) (496431697681/1000000000000 : ℝ) (496431697689/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 2 (125885759903/250000000000 : ℝ) (503543039619/1000000000000 : ℝ) (496431697681/1000000000000 : ℝ) (496431697689/1000000000000 : ℝ) (249993684323/500000000000 : ℝ) (249993684327/500000000000 : ℝ) (499974725371/1000000000000 : ℝ) (499974725379/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 3 (249993684323/500000000000 : ℝ) (249993684327/500000000000 : ℝ) (499974725371/1000000000000 : ℝ) (499974725379/1000000000000 : ℝ) (15624407719/31250000000 : ℝ) (499981047017/1000000000000 : ℝ) (62497630871/125000000000 : ℝ) (499981046977/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 4 (15624407719/31250000000 : ℝ) (499981047017/1000000000000 : ℝ) (62497630871/125000000000 : ℝ) (499981046977/1000000000000 : ℝ) (124995261747/250000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 5 (124995261747/250000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 6 (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (257/2048 : ℝ))) 7 (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (257/2048 : ℝ)) hmem 8 (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (257/2048 : ℝ))) hcmem 8 (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (257/2048 : ℝ)) (992202916743/1000000000000 : ℝ) (496101458373/500000000000 : ℝ) (499981046987/1000000000000 : ℝ) (499981046997/1000000000000 : ℝ) (395770048051/500000000000 : ℝ) (791540096121/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0221_exp_lower
  have heNumeric : (2054900210619/1000000000000 : ℝ)/4 ≤ Real.exp (-10657073178561/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900210619/1000000000000 : ℝ)/4 ≤ Real.exp ((8223/65536 : ℝ)-(791540096121/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8223/65536 : ℝ) (257/2048 : ℝ) (791540096121/1000000000000 : ℝ) (2054900210619/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0222; no trusted numerical premise.
theorem cover8_leaf0222_exp_radius : (499020523826419307/500000000000000000 : ℝ) ≤ Real.exp ((-16449/1048576 : ℝ)/8) ∧ Real.exp ((-16449/1048576 : ℝ)/8) ≤ (199608209530567723/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16449/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0222_exp_lower : (920114240944451041/1000000000000000000 : ℝ) ≤ Real.exp ((-166514883417/250000000000 : ℝ)/8) ∧ Real.exp ((-166514883417/250000000000 : ℝ)/8) ≤ (460057120472225521/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166514883417/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0222_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915704609/1000000000000 : ℝ) ≤ 4*Real.exp (257/2048 : ℝ)*Real.exp (-mu (radius 8 (16449/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915704609/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16449/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0222_exp_radius
  have hrNumeric : (492217705557/500000000000 : ℝ) ≤ Real.exp (-16449/1048576 : ℝ) ∧ Real.exp (-16449/1048576 : ℝ) ≤ (196887082223/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492217705557/500000000000 : ℝ) ≤ (radius 8 (16449/131072 : ℝ)) ∧ (radius 8 (16449/131072 : ℝ)) ≤ (196887082223/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16449/131072 : ℝ)) (492217705557/500000000000 : ℝ) (196887082223/200000000000 : ℝ) (87873376717/500000000000 : ℝ) (175746753441/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16449/131072 : ℝ)) (492217705557/500000000000 : ℝ) (196887082223/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492217705557/500000000000 : ℝ) (196887082223/200000000000 : ℝ) (992217705557/1000000000000 : ℝ) (496108852779/500000000000 : ℝ) (992187185521/1000000000000 : ℝ) (992187185523/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 1 (992217705557/1000000000000 : ℝ) (496108852779/500000000000 : ℝ) (992187185521/1000000000000 : ℝ) (992187185523/1000000000000 : ℝ) (992202445539/1000000000000 : ℝ) (992202445541/1000000000000 : ℝ) (992202445421/1000000000000 : ℝ) (62012652839/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 2 (992202445539/1000000000000 : ℝ) (992202445541/1000000000000 : ℝ) (992202445421/1000000000000 : ℝ) (62012652839/62500000000 : ℝ) (24805061137/25000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 3 (24805061137/25000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 4 (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 5 (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 6 (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16449/131072 : ℝ)) 7 (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16449/131072 : ℝ))) (87873376717/500000000000 : ℝ) (175746753441/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87873376717/500000000000 : ℝ) (175746753441/1000000000000 : ℝ) (587873376717/1000000000000 : ℝ) (587873376721/1000000000000 : ℝ) (419221604207/1000000000000 : ℝ) (52402700527/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 1 (587873376717/1000000000000 : ℝ) (587873376721/1000000000000 : ℝ) (419221604207/1000000000000 : ℝ) (52402700527/125000000000 : ℝ) (251773745231/500000000000 : ℝ) (503547490469/1000000000000 : ℝ) (6205456521/12500000000 : ℝ) (62054565211/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 2 (251773745231/500000000000 : ℝ) (503547490469/1000000000000 : ℝ) (6205456521/12500000000 : ℝ) (62054565211/125000000000 : ℝ) (499992006071/1000000000000 : ℝ) (499992006079/1000000000000 : ℝ) (499979364239/1000000000000 : ℝ) (62497420531/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 3 (499992006071/1000000000000 : ℝ) (499992006079/1000000000000 : ℝ) (499979364239/1000000000000 : ℝ) (62497420531/125000000000 : ℝ) (99997137031/200000000000 : ℝ) (124996421291/250000000000 : ℝ) (99997137023/200000000000 : ℝ) (124996421281/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 4 (99997137031/200000000000 : ℝ) (124996421291/250000000000 : ℝ) (99997137023/200000000000 : ℝ) (124996421281/250000000000 : ℝ) (99997137027/200000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 5 (99997137027/200000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 6 (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16449/131072 : ℝ))) 7 (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16449/131072 : ℝ)) hmem 8 (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16449/131072 : ℝ))) hcmem 8 (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16449/131072 : ℝ)) (992202445479/1000000000000 : ℝ) (992202445483/1000000000000 : ℝ) (249992842567/500000000000 : ℝ) (62498210643/125000000000 : ℝ) (791547814897/1000000000000 : ℝ) (395773907459/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0222_exp_lower
  have heNumeric : (2054915704609/1000000000000 : ℝ)/4 ≤ Real.exp (-166514883417/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915704609/1000000000000 : ℝ)/4 ≤ Real.exp ((257/2048 : ℝ)-(395773907459/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (257/2048 : ℝ) (16449/131072 : ℝ) (395773907459/500000000000 : ℝ) (2054915704609/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0223; no trusted numerical premise.
theorem cover8_leaf0223_exp_radius : (7797194755289699/7812500000000000 : ℝ) ≤ Real.exp ((-8225/524288 : ℝ)/8) ∧ Real.exp ((-8225/524288 : ℝ)/8) ≤ (998040928677081473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8225/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0223_exp_lower : (184022846139693011/200000000000000000 : ℝ) ≤ Real.exp ((-21313907928079/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313907928079/32000000000000 : ℝ)/8) ≤ (28753569709327033/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313907928079/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0223_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915521547/1000000000000 : ℝ) ≤ 4*Real.exp (16449/131072 : ℝ)*Real.exp (-mu (radius 8 (8225/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915521547/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8225/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0223_exp_radius
  have hrNumeric : (984434472283/1000000000000 : ℝ) ≤ Real.exp (-8225/524288 : ℝ) ∧ Real.exp (-8225/524288 : ℝ) ≤ (246108618071/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984434472283/1000000000000 : ℝ) ≤ (radius 8 (8225/65536 : ℝ)) ∧ (radius 8 (8225/65536 : ℝ)) ≤ (246108618071/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8225/65536 : ℝ)) (984434472283/1000000000000 : ℝ) (246108618071/250000000000 : ℝ) (175752012161/1000000000000 : ℝ) (21969001521/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8225/65536 : ℝ)) (984434472283/1000000000000 : ℝ) (246108618071/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984434472283/1000000000000 : ℝ) (246108618071/250000000000 : ℝ) (992217236141/1000000000000 : ℝ) (496108618071/500000000000 : ℝ) (99218671241/100000000000 : ℝ) (992186712411/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 1 (992217236141/1000000000000 : ℝ) (496108618071/500000000000 : ℝ) (99218671241/100000000000 : ℝ) (992186712411/1000000000000 : ℝ) (39688078971/40000000000 : ℝ) (992201974277/1000000000000 : ℝ) (496100987079/500000000000 : ℝ) (12402524677/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 2 (39688078971/40000000000 : ℝ) (992201974277/1000000000000 : ℝ) (496100987079/500000000000 : ℝ) (12402524677/12500000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 3 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 4 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 5 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 6 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8225/65536 : ℝ)) 7 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8225/65536 : ℝ))) (175752012161/1000000000000 : ℝ) (21969001521/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175752012161/1000000000000 : ℝ) (21969001521/125000000000 : ℝ) (1837112519/3125000000 : ℝ) (146969001521/250000000000 : ℝ) (419227876173/1000000000000 : ℝ) (209613938091/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 1 (1837112519/3125000000 : ℝ) (146969001521/250000000000 : ℝ) (419227876173/1000000000000 : ℝ) (209613938091/500000000000 : ℝ) (251775970563/500000000000 : ℝ) (503551941133/1000000000000 : ℝ) (496441345459/1000000000000 : ℝ) (496441345467/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 2 (251775970563/500000000000 : ℝ) (503551941133/1000000000000 : ℝ) (496441345459/1000000000000 : ℝ) (496441345467/1000000000000 : ℝ) (124999160823/250000000000 : ℝ) (4999966433/10000000000 : ℝ) (99996800581/200000000000 : ℝ) (499984002913/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 3 (124999160823/250000000000 : ℝ) (4999966433/10000000000 : ℝ) (99996800581/200000000000 : ℝ) (499984002913/1000000000000 : ℝ) (249995161549/500000000000 : ℝ) (499990323107/1000000000000 : ℝ) (249995161529/500000000000 : ℝ) (499990323067/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 4 (249995161549/500000000000 : ℝ) (499990323107/1000000000000 : ℝ) (249995161529/500000000000 : ℝ) (499990323067/1000000000000 : ℝ) (249995161539/500000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 5 (249995161539/500000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 6 (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8225/65536 : ℝ))) 7 (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8225/65536 : ℝ)) hmem 8 (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8225/65536 : ℝ))) hcmem 8 (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8225/65536 : ℝ)) (124025246777/125000000000 : ℝ) (992201974219/1000000000000 : ℝ) (499990323077/1000000000000 : ℝ) (499990323087/1000000000000 : ℝ) (395777766689/500000000000 : ℝ) (791555533397/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0223_exp_lower
  have heNumeric : (2054915521547/1000000000000 : ℝ)/4 ≤ Real.exp (-21313907928079/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915521547/1000000000000 : ℝ)/4 ≤ Real.exp ((16449/131072 : ℝ)-(791555533397/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16449/131072 : ℝ) (8225/65536 : ℝ) (791555533397/1000000000000 : ℝ) (2054915521547/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0224; no trusted numerical premise.
theorem cover8_leaf0224_exp_radius : (499020404850669257/500000000000000000 : ℝ) ≤ Real.exp ((-16451/1048576 : ℝ)/8) ∧ Real.exp ((-16451/1048576 : ℝ)/8) ≤ (199608161940267703/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16451/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0224_exp_lower : (920114220489513781/1000000000000000000 : ℝ) ≤ Real.exp ((-10656955384239/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656955384239/16000000000000 : ℝ)/8) ≤ (460057110244756891/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656955384239/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0224_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728834787/250000000000 : ℝ) ≤ 4*Real.exp (8225/65536 : ℝ)*Real.exp (-mu (radius 8 (16451/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728834787/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16451/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0224_exp_radius
  have hrNumeric : (492216766727/500000000000 : ℝ) ≤ Real.exp (-16451/1048576 : ℝ) ∧ Real.exp (-16451/1048576 : ℝ) ≤ (196886706691/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492216766727/500000000000 : ℝ) ≤ (radius 8 (16451/131072 : ℝ)) ∧ (radius 8 (16451/131072 : ℝ)) ≤ (196886706691/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16451/131072 : ℝ)) (492216766727/500000000000 : ℝ) (196886706691/200000000000 : ℝ) (35151454143/200000000000 : ℝ) (175757270721/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16451/131072 : ℝ)) (492216766727/500000000000 : ℝ) (196886706691/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492216766727/500000000000 : ℝ) (196886706691/200000000000 : ℝ) (992216766727/1000000000000 : ℝ) (124027095841/125000000000 : ℝ) (496093119649/500000000000 : ℝ) (9921862393/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 1 (992216766727/1000000000000 : ℝ) (124027095841/125000000000 : ℝ) (496093119649/500000000000 : ℝ) (9921862393/10000000000 : ℝ) (248050375753/250000000000 : ℝ) (496100751507/500000000000 : ℝ) (198440300579/200000000000 : ℝ) (992201502897/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 2 (248050375753/250000000000 : ℝ) (496100751507/500000000000 : ℝ) (198440300579/200000000000 : ℝ) (992201502897/1000000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 3 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 4 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 5 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 6 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16451/131072 : ℝ)) 7 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16451/131072 : ℝ))) (35151454143/200000000000 : ℝ) (175757270721/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35151454143/200000000000 : ℝ) (175757270721/1000000000000 : ℝ) (587878635357/1000000000000 : ℝ) (587878635361/1000000000000 : ℝ) (419234147839/1000000000000 : ℝ) (419234147847/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 1 (587878635357/1000000000000 : ℝ) (587878635361/1000000000000 : ℝ) (419234147839/1000000000000 : ℝ) (419234147847/1000000000000 : ℝ) (251778195799/500000000000 : ℝ) (125889097901/250000000000 : ℝ) (496446169011/1000000000000 : ℝ) (496446169019/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 2 (251778195799/500000000000 : ℝ) (125889097901/250000000000 : ℝ) (496446169011/1000000000000 : ℝ) (496446169019/1000000000000 : ℝ) (31250080019/62500000000 : ℝ) (62500160039/125000000000 : ℝ) (6249858017/12500000000 : ℝ) (62498580171/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 3 (31250080019/62500000000 : ℝ) (62500160039/125000000000 : ℝ) (6249858017/12500000000 : ℝ) (62498580171/125000000000 : ℝ) (7812421263/15625000000 : ℝ) (12499874021/25000000000 : ℝ) (62499370099/125000000000 : ℝ) (499994960801/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 4 (7812421263/15625000000 : ℝ) (12499874021/25000000000 : ℝ) (62499370099/125000000000 : ℝ) (499994960801/1000000000000 : ℝ) (124998740203/250000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 5 (124998740203/250000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 6 (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16451/131072 : ℝ))) 7 (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16451/131072 : ℝ)) hmem 8 (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16451/131072 : ℝ))) hcmem 8 (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16451/131072 : ℝ)) (992201502953/1000000000000 : ℝ) (248050375739/250000000000 : ℝ) (499994960811/1000000000000 : ℝ) (499994960821/1000000000000 : ℝ) (158312650307/200000000000 : ℝ) (395781625777/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0224_exp_lower
  have heNumeric : (513728834787/250000000000 : ℝ)/4 ≤ Real.exp (-10656955384239/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728834787/250000000000 : ℝ)/4 ≤ Real.exp ((8225/65536 : ℝ)-(395781625777/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8225/65536 : ℝ) (16451/131072 : ℝ) (395781625777/500000000000 : ℝ) (513728834787/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0200_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0200_certificate
#check SmaleRate.Proofs.cover8_leaf0201_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0201_certificate
#check SmaleRate.Proofs.cover8_leaf0202_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0202_certificate
#check SmaleRate.Proofs.cover8_leaf0203_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0203_certificate
#check SmaleRate.Proofs.cover8_leaf0204_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0204_certificate
#check SmaleRate.Proofs.cover8_leaf0205_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0205_certificate
#check SmaleRate.Proofs.cover8_leaf0206_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0206_certificate
#check SmaleRate.Proofs.cover8_leaf0207_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0207_certificate
#check SmaleRate.Proofs.cover8_leaf0208_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0208_certificate
#check SmaleRate.Proofs.cover8_leaf0209_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0209_certificate
#check SmaleRate.Proofs.cover8_leaf0210_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0210_certificate
#check SmaleRate.Proofs.cover8_leaf0211_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0211_certificate
#check SmaleRate.Proofs.cover8_leaf0212_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0212_certificate
#check SmaleRate.Proofs.cover8_leaf0213_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0213_certificate
#check SmaleRate.Proofs.cover8_leaf0214_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0214_certificate
#check SmaleRate.Proofs.cover8_leaf0215_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0215_certificate
#check SmaleRate.Proofs.cover8_leaf0216_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0216_certificate
#check SmaleRate.Proofs.cover8_leaf0217_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0217_certificate
#check SmaleRate.Proofs.cover8_leaf0218_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0218_certificate
#check SmaleRate.Proofs.cover8_leaf0219_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0219_certificate
#check SmaleRate.Proofs.cover8_leaf0220_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0220_certificate
#check SmaleRate.Proofs.cover8_leaf0221_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0221_certificate
#check SmaleRate.Proofs.cover8_leaf0222_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0222_certificate
#check SmaleRate.Proofs.cover8_leaf0223_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0223_certificate
#check SmaleRate.Proofs.cover8_leaf0224_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0224_certificate
