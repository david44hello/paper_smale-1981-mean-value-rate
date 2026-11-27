/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1450; no trusted numerical premise.
theorem cover8_leaf1450_exp_radius : (997979063204559327/1000000000000000000 : ℝ) ≤ Real.exp ((-8485/524288 : ℝ)/8) ∧ Real.exp ((-8485/524288 : ℝ)/8) ≤ (31186845725142479/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8485/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1450_exp_lower : (184022755662565411/200000000000000000 : ℝ) ≤ Real.exp ((-21314033793703/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314033793703/32000000000000 : ℝ)/8) ≤ (57507111144551691/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314033793703/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1450_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907438963/1000000000000 : ℝ) ≤ 4*Real.exp (16969/131072 : ℝ)*Real.exp (-mu (radius 8 (8485/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907438963/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8485/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1450_exp_radius
  have hrNumeric : (983946401779/1000000000000 : ℝ) ≤ Real.exp (-8485/524288 : ℝ) ∧ Real.exp (-8485/524288 : ℝ) ≤ (49197320089/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983946401779/1000000000000 : ℝ) ≤ (radius 8 (8485/65536 : ℝ)) ∧ (radius 8 (8485/65536 : ℝ)) ≤ (49197320089/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8485/65536 : ℝ)) (983946401779/1000000000000 : ℝ) (49197320089/50000000000 : ℝ) (44616055423/250000000000 : ℝ) (89232110849/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8485/65536 : ℝ)) (983946401779/1000000000000 : ℝ) (49197320089/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983946401779/1000000000000 : ℝ) (49197320089/50000000000 : ℝ) (991973200889/1000000000000 : ℝ) (99197320089/100000000000 : ℝ) (247985181233/250000000000 : ℝ) (991940724933/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 1 (991973200889/1000000000000 : ℝ) (99197320089/100000000000 : ℝ) (247985181233/250000000000 : ℝ) (991940724933/1000000000000 : ℝ) (99195696291/100000000000 : ℝ) (30998655091/31250000000 : ℝ) (991956962777/1000000000000 : ℝ) (991956962779/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 2 (99195696291/100000000000 : ℝ) (30998655091/31250000000 : ℝ) (991956962777/1000000000000 : ℝ) (991956962779/1000000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 3 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 4 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 5 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 6 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8485/65536 : ℝ)) 7 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8485/65536 : ℝ))) (44616055423/250000000000 : ℝ) (89232110849/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44616055423/250000000000 : ℝ) (89232110849/500000000000 : ℝ) (294616055423/500000000000 : ℝ) (589232110849/1000000000000 : ℝ) (422450259429/1000000000000 : ℝ) (422450259437/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 1 (294616055423/500000000000 : ℝ) (589232110849/1000000000000 : ℝ) (422450259429/1000000000000 : ℝ) (422450259437/1000000000000 : ℝ) (505841185137/1000000000000 : ℝ) (505841185143/1000000000000 : ℝ) (498920091889/1000000000000 : ℝ) (62365011487/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 2 (505841185137/1000000000000 : ℝ) (505841185143/1000000000000 : ℝ) (498920091889/1000000000000 : ℝ) (62365011487/125000000000 : ℝ) (502380638513/1000000000000 : ℝ) (12559515963/25000000000 : ℝ) (62796089967/125000000000 : ℝ) (3924755623/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 3 (502380638513/1000000000000 : ℝ) (12559515963/25000000000 : ℝ) (62796089967/125000000000 : ℝ) (3924755623/7812500000 : ℝ) (125593669781/250000000000 : ℝ) (125593669783/250000000000 : ℝ) (502374679089/1000000000000 : ℝ) (502374679097/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 4 (125593669781/250000000000 : ℝ) (125593669783/250000000000 : ℝ) (502374679089/1000000000000 : ℝ) (502374679097/1000000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 5 (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 6 (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8485/65536 : ℝ))) 7 (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8485/65536 : ℝ)) hmem 8 (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8485/65536 : ℝ))) hcmem 8 (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8485/65536 : ℝ)) (991956962843/1000000000000 : ℝ) (495978481423/500000000000 : ℝ) (251187339553/500000000000 : ℝ) (100474935823/200000000000 : ℝ) (198881687959/250000000000 : ℝ) (397763375927/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1450_exp_lower
  have heNumeric : (2054907438963/1000000000000 : ℝ)/4 ≤ Real.exp (-21314033793703/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907438963/1000000000000 : ℝ)/4 ≤ Real.exp ((16969/131072 : ℝ)-(397763375927/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16969/131072 : ℝ) (8485/65536 : ℝ) (397763375927/500000000000 : ℝ) (2054907438963/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1451; no trusted numerical premise.
theorem cover8_leaf1451_exp_radius : (997978944236191307/1000000000000000000 : ℝ) ≤ Real.exp ((-16971/1048576 : ℝ)/8) ∧ Real.exp ((-16971/1048576 : ℝ)/8) ≤ (249494736059047827/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16971/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1451_exp_lower : (920113786649004011/1000000000000000000 : ℝ) ≤ Real.exp ((-10657015737179/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657015737179/16000000000000 : ℝ)/8) ≤ (230028446662251003/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657015737179/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1451_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907587901/1000000000000 : ℝ) ≤ 4*Real.exp (8485/65536 : ℝ)*Real.exp (-mu (radius 8 (16971/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907587901/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16971/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1451_exp_radius
  have hrNumeric : (196789092683/200000000000 : ℝ) ≤ Real.exp (-16971/1048576 : ℝ) ∧ Real.exp (-16971/1048576 : ℝ) ≤ (122993182927/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196789092683/200000000000 : ℝ) ≤ (radius 8 (16971/131072 : ℝ)) ∧ (radius 8 (16971/131072 : ℝ)) ≤ (122993182927/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16971/131072 : ℝ)) (196789092683/200000000000 : ℝ) (122993182927/125000000000 : ℝ) (27885843/156250000 : ℝ) (89234697603/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16971/131072 : ℝ)) (196789092683/200000000000 : ℝ) (122993182927/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196789092683/200000000000 : ℝ) (122993182927/125000000000 : ℝ) (991972731707/1000000000000 : ℝ) (247993182927/250000000000 : ℝ) (495970125969/500000000000 : ℝ) (991940251939/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 1 (991972731707/1000000000000 : ℝ) (247993182927/250000000000 : ℝ) (495970125969/500000000000 : ℝ) (991940251939/1000000000000 : ℝ) (495978245911/500000000000 : ℝ) (61997280739/62500000000 : ℝ) (991956491689/1000000000000 : ℝ) (991956491691/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 2 (495978245911/500000000000 : ℝ) (61997280739/62500000000 : ℝ) (991956491689/1000000000000 : ℝ) (991956491691/1000000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 3 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 4 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 5 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 6 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16971/131072 : ℝ)) 7 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16971/131072 : ℝ))) (27885843/156250000 : ℝ) (89234697603/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (27885843/156250000 : ℝ) (89234697603/500000000000 : ℝ) (184135843/312500000 : ℝ) (589234697603/1000000000000 : ℝ) (2112281913/5000000000 : ℝ) (26403523913/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 1 (184135843/312500000 : ℝ) (589234697603/1000000000000 : ℝ) (2112281913/5000000000 : ℝ) (26403523913/62500000000 : ℝ) (5058455401/10000000000 : ℝ) (252922770053/500000000000 : ℝ) (498924802801/1000000000000 : ℝ) (62365600351/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 2 (5058455401/10000000000 : ℝ) (252922770053/500000000000 : ℝ) (498924802801/1000000000000 : ℝ) (62365600351/125000000000 : ℝ) (10047703429/20000000000 : ℝ) (502385171457/1000000000000 : ℝ) (502373254007/1000000000000 : ℝ) (100474650803/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 3 (10047703429/20000000000 : ℝ) (502385171457/1000000000000 : ℝ) (502373254007/1000000000000 : ℝ) (100474650803/200000000000 : ℝ) (62797401591/125000000000 : ℝ) (7849675199/15625000000 : ℝ) (502379212693/1000000000000 : ℝ) (502379212701/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 4 (62797401591/125000000000 : ℝ) (7849675199/15625000000 : ℝ) (502379212693/1000000000000 : ℝ) (502379212701/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 5 (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 6 (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16971/131072 : ℝ))) 7 (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16971/131072 : ℝ)) hmem 8 (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16971/131072 : ℝ))) hcmem 8 (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16971/131072 : ℝ)) (198391298351/200000000000 : ℝ) (495978245879/500000000000 : ℝ) (50237921271/100000000000 : ℝ) (502379212719/1000000000000 : ℝ) (49720894297/62500000000 : ℝ) (795534308769/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1451_exp_lower
  have heNumeric : (2054907587901/1000000000000 : ℝ)/4 ≤ Real.exp (-10657015737179/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907587901/1000000000000 : ℝ)/4 ≤ Real.exp ((8485/65536 : ℝ)-(795534308769/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8485/65536 : ℝ) (16971/131072 : ℝ) (795534308769/1000000000000 : ℝ) (2054907587901/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1452; no trusted numerical premise.
theorem cover8_leaf1452_exp_radius : (997978825267837469/1000000000000000000 : ℝ) ≤ Real.exp ((-4243/262144 : ℝ)/8) ∧ Real.exp ((-4243/262144 : ℝ)/8) ≤ (99797882526783747/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4243/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1452_exp_lower : (230028448754950081/250000000000000000 : ℝ) ≤ Real.exp ((-21314029145381/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314029145381/32000000000000 : ℝ)/8) ≤ (36804551800792013/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314029145381/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1452_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907737459/1000000000000 : ℝ) ≤ 4*Real.exp (16971/131072 : ℝ)*Real.exp (-mu (radius 8 (4243/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907737459/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4243/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1452_exp_radius
  have hrNumeric : (245986131263/250000000000 : ℝ) ≤ Real.exp (-4243/262144 : ℝ) ∧ Real.exp (-4243/262144 : ℝ) ≤ (983944525053/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245986131263/250000000000 : ℝ) ≤ (radius 8 (4243/32768 : ℝ)) ∧ (radius 8 (4243/32768 : ℝ)) ≤ (983944525053/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4243/32768 : ℝ)) (245986131263/250000000000 : ℝ) (983944525053/1000000000000 : ℝ) (178474568547/1000000000000 : ℝ) (89237284277/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4243/32768 : ℝ)) (245986131263/250000000000 : ℝ) (983944525053/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245986131263/250000000000 : ℝ) (983944525053/1000000000000 : ℝ) (495986131263/500000000000 : ℝ) (991972262527/1000000000000 : ℝ) (7749529523/7812500000 : ℝ) (198387955789/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 1 (495986131263/500000000000 : ℝ) (991972262527/1000000000000 : ℝ) (7749529523/7812500000 : ℝ) (198387955789/200000000000 : ℝ) (198391204147/200000000000 : ℝ) (1937414103/1953125000 : ℝ) (495978010301/500000000000 : ℝ) (247989005151/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 2 (198391204147/200000000000 : ℝ) (1937414103/1953125000 : ℝ) (495978010301/500000000000 : ℝ) (247989005151/250000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 3 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 4 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 5 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 6 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4243/32768 : ℝ)) 7 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4243/32768 : ℝ))) (178474568547/1000000000000 : ℝ) (89237284277/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178474568547/1000000000000 : ℝ) (89237284277/500000000000 : ℝ) (589237284273/1000000000000 : ℝ) (589237284277/1000000000000 : ℝ) (105615626373/250000000000 : ℝ) (422462505501/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 1 (589237284273/1000000000000 : ℝ) (589237284277/1000000000000 : ℝ) (105615626373/250000000000 : ℝ) (422462505501/1000000000000 : ℝ) (252924947441/500000000000 : ℝ) (505849894889/1000000000000 : ℝ) (498929513501/1000000000000 : ℝ) (498929513509/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 2 (252924947441/500000000000 : ℝ) (505849894889/1000000000000 : ℝ) (498929513501/1000000000000 : ℝ) (498929513509/1000000000000 : ℝ) (502389704191/1000000000000 : ℝ) (502389704199/1000000000000 : ℝ) (502377788081/1000000000000 : ℝ) (50237778809/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 3 (502389704191/1000000000000 : ℝ) (502389704199/1000000000000 : ℝ) (502377788081/1000000000000 : ℝ) (50237778809/100000000000 : ℝ) (62797968267/125000000000 : ℝ) (100476749229/200000000000 : ℝ) (5023837461/10000000000 : ℝ) (50238374611/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 4 (62797968267/125000000000 : ℝ) (100476749229/200000000000 : ℝ) (5023837461/10000000000 : ℝ) (50238374611/100000000000 : ℝ) (251191873059/500000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 5 (251191873059/500000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 6 (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4243/32768 : ℝ))) 7 (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4243/32768 : ℝ)) hmem 8 (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4243/32768 : ℝ))) hcmem 8 (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4243/32768 : ℝ)) (247989005167/250000000000 : ℝ) (99195602067/100000000000 : ℝ) (502383746117/1000000000000 : ℝ) (31398984133/62500000000 : ℝ) (795541865363/1000000000000 : ℝ) (795541865383/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1452_exp_lower
  have heNumeric : (2054907737459/1000000000000 : ℝ)/4 ≤ Real.exp (-21314029145381/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907737459/1000000000000 : ℝ)/4 ≤ Real.exp ((16971/131072 : ℝ)-(795541865383/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16971/131072 : ℝ) (4243/32768 : ℝ) (795541865383/1000000000000 : ℝ) (2054907737459/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1453; no trusted numerical premise.
theorem cover8_leaf1453_exp_radius : (498989353149748907/500000000000000000 : ℝ) ≤ Real.exp ((-16973/1048576 : ℝ)/8) ∧ Real.exp ((-16973/1048576 : ℝ)/8) ≤ (199595741259899563/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16973/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1453_exp_lower : (92011380342533101/100000000000000000 : ℝ) ≤ Real.exp ((-1065701340337/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065701340337/1600000000000 : ℝ)/8) ≤ (920113803425331011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065701340337/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1453_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726971909/250000000000 : ℝ) ≤ 4*Real.exp (4243/32768 : ℝ)*Real.exp (-mu (radius 8 (16973/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726971909/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16973/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1453_exp_radius
  have hrNumeric : (98394358669/100000000000 : ℝ) ≤ Real.exp (-16973/1048576 : ℝ) ∧ Real.exp (-16973/1048576 : ℝ) ≤ (983943586691/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98394358669/100000000000 : ℝ) ≤ (radius 8 (16973/131072 : ℝ)) ∧ (radius 8 (16973/131072 : ℝ)) ≤ (983943586691/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16973/131072 : ℝ)) (98394358669/100000000000 : ℝ) (983943586691/1000000000000 : ℝ) (89239870867/500000000000 : ℝ) (178479741741/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16973/131072 : ℝ)) (98394358669/100000000000 : ℝ) (983943586691/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98394358669/100000000000 : ℝ) (983943586691/1000000000000 : ℝ) (198394358669/200000000000 : ℝ) (495985896673/500000000000 : ℝ) (19838786119/20000000000 : ℝ) (30998103311/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 1 (198394358669/200000000000 : ℝ) (495985896673/500000000000 : ℝ) (19838786119/20000000000 : ℝ) (30998103311/31250000000 : ℝ) (991955549647/1000000000000 : ℝ) (991955549649/1000000000000 : ℝ) (495977774757/500000000000 : ℝ) (991955549517/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 2 (991955549647/1000000000000 : ℝ) (991955549649/1000000000000 : ℝ) (495977774757/500000000000 : ℝ) (991955549517/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 3 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 4 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 5 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 6 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16973/131072 : ℝ)) 7 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16973/131072 : ℝ))) (89239870867/500000000000 : ℝ) (178479741741/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89239870867/500000000000 : ℝ) (178479741741/1000000000000 : ℝ) (589239870867/1000000000000 : ℝ) (589239870871/1000000000000 : ℝ) (211234314053/500000000000 : ℝ) (84493725623/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 1 (589239870867/1000000000000 : ℝ) (589239870871/1000000000000 : ℝ) (211234314053/500000000000 : ℝ) (84493725623/200000000000 : ℝ) (252927124743/500000000000 : ℝ) (505854249493/1000000000000 : ℝ) (62366777999/125000000000 : ℝ) (31183389/62500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 2 (252927124743/500000000000 : ℝ) (505854249493/1000000000000 : ℝ) (62366777999/125000000000 : ℝ) (31183389/62500000 : ℝ) (502394236739/1000000000000 : ℝ) (502394236747/1000000000000 : ℝ) (251191160981/500000000000 : ℝ) (50238232197/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 3 (502394236739/1000000000000 : ℝ) (502394236747/1000000000000 : ℝ) (251191160981/500000000000 : ℝ) (50238232197/100000000000 : ℝ) (10047765587/20000000000 : ℝ) (502388279359/1000000000000 : ℝ) (100477655863/200000000000 : ℝ) (125597069831/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 4 (10047765587/20000000000 : ℝ) (502388279359/1000000000000 : ℝ) (100477655863/200000000000 : ℝ) (125597069831/250000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 5 (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 6 (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16973/131072 : ℝ))) 7 (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16973/131072 : ℝ)) hmem 8 (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16973/131072 : ℝ))) hcmem 8 (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16973/131072 : ℝ)) (49597777479/50000000000 : ℝ) (991955549583/1000000000000 : ℝ) (125597069833/250000000000 : ℝ) (251194139671/500000000000 : ℝ) (198887355419/250000000000 : ℝ) (159109884339/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1453_exp_lower
  have heNumeric : (513726971909/250000000000 : ℝ)/4 ≤ Real.exp (-1065701340337/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726971909/250000000000 : ℝ)/4 ≤ Real.exp ((4243/32768 : ℝ)-(159109884339/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4243/32768 : ℝ) (16973/131072 : ℝ) (159109884339/200000000000 : ℝ) (513726971909/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1454; no trusted numerical premise.
theorem cover8_leaf1454_exp_radius : (49898929366558617/50000000000000000 : ℝ) ≤ Real.exp ((-8487/524288 : ℝ)/8) ∧ Real.exp ((-8487/524288 : ℝ)/8) ≤ (997978587331172341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8487/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1454_exp_lower : (920113811865941111/1000000000000000000 : ℝ) ≤ Real.exp ((-21314024458339/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314024458339/32000000000000 : ℝ)/8) ≤ (115014226483242639/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314024458339/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1454_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908038441/1000000000000 : ℝ) ≤ 4*Real.exp (16973/131072 : ℝ)*Real.exp (-mu (radius 8 (8487/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908038441/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8487/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1454_exp_radius
  have hrNumeric : (983942648329/1000000000000 : ℝ) ≤ Real.exp (-8487/524288 : ℝ) ∧ Real.exp (-8487/524288 : ℝ) ≤ (98394264833/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983942648329/1000000000000 : ℝ) ≤ (radius 8 (8487/65536 : ℝ)) ∧ (radius 8 (8487/65536 : ℝ)) ≤ (98394264833/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8487/65536 : ℝ)) (983942648329/1000000000000 : ℝ) (98394264833/100000000000 : ℝ) (178484914761/1000000000000 : ℝ) (178484914767/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8487/65536 : ℝ)) (983942648329/1000000000000 : ℝ) (98394264833/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983942648329/1000000000000 : ℝ) (98394264833/100000000000 : ℝ) (247992831041/250000000000 : ℝ) (198394264833/200000000000 : ℝ) (991938832957/1000000000000 : ℝ) (495969416479/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 1 (247992831041/250000000000 : ℝ) (198394264833/200000000000 : ℝ) (991938832957/1000000000000 : ℝ) (495969416479/500000000000 : ℝ) (6199719241/6250000000 : ℝ) (495977539281/500000000000 : ℝ) (991955078427/1000000000000 : ℝ) (991955078429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 2 (6199719241/6250000000 : ℝ) (495977539281/500000000000 : ℝ) (991955078427/1000000000000 : ℝ) (991955078429/1000000000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 3 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 4 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 5 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 6 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8487/65536 : ℝ)) 7 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8487/65536 : ℝ))) (178484914761/1000000000000 : ℝ) (178484914767/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178484914761/1000000000000 : ℝ) (178484914767/1000000000000 : ℝ) (29462122869/50000000000 : ℝ) (73655307173/125000000000 : ℝ) (422474750441/1000000000000 : ℝ) (8449495009/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 1 (29462122869/50000000000 : ℝ) (73655307173/125000000000 : ℝ) (422474750441/1000000000000 : ℝ) (8449495009/20000000000 : ℝ) (50585860391/100000000000 : ℝ) (505858603917/1000000000000 : ℝ) (49893893427/100000000000 : ℝ) (249469467139/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 2 (50585860391/100000000000 : ℝ) (505858603917/1000000000000 : ℝ) (49893893427/100000000000 : ℝ) (249469467139/500000000000 : ℝ) (50239876909/100000000000 : ℝ) (251199384549/500000000000 : ℝ) (251193427823/500000000000 : ℝ) (251193427827/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 3 (50239876909/100000000000 : ℝ) (251199384549/500000000000 : ℝ) (251193427823/500000000000 : ℝ) (251193427827/500000000000 : ℝ) (31399550773/62500000000 : ℝ) (62799101547/125000000000 : ℝ) (125598203083/250000000000 : ℝ) (502392812341/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 4 (31399550773/62500000000 : ℝ) (62799101547/125000000000 : ℝ) (125598203083/250000000000 : ℝ) (502392812341/1000000000000 : ℝ) (10047856247/20000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 5 (10047856247/20000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 6 (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8487/65536 : ℝ))) 7 (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8487/65536 : ℝ)) hmem 8 (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8487/65536 : ℝ))) hcmem 8 (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8487/65536 : ℝ)) (991955078493/1000000000000 : ℝ) (30998596203/31250000000 : ℝ) (502392812349/1000000000000 : ℝ) (502392812359/1000000000000 : ℝ) (795556977683/1000000000000 : ℝ) (397778488851/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1454_exp_lower
  have heNumeric : (2054908038441/1000000000000 : ℝ)/4 ≤ Real.exp (-21314024458339/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908038441/1000000000000 : ℝ)/4 ≤ Real.exp ((16973/131072 : ℝ)-(397778488851/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16973/131072 : ℝ) (8487/65536 : ℝ) (397778488851/500000000000 : ℝ) (2054908038441/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1455; no trusted numerical premise.
theorem cover8_leaf1455_exp_radius : (124747308545357631/125000000000000000 : ℝ) ≤ Real.exp ((-16975/1048576 : ℝ)/8) ∧ Real.exp ((-16975/1048576 : ℝ)/8) ≤ (997978468362861049/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16975/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1455_exp_lower : (184022764068027089/200000000000000000 : ℝ) ≤ Real.exp ((-10657011050297/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657011050297/16000000000000 : ℝ)/8) ≤ (460056910170067723/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657011050297/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1455_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454094923/500000000000 : ℝ) ≤ 4*Real.exp (8487/65536 : ℝ)*Real.exp (-mu (radius 8 (16975/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454094923/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16975/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1455_exp_radius
  have hrNumeric : (61496356873/62500000000 : ℝ) ≤ Real.exp (-16975/1048576 : ℝ) ∧ Real.exp (-16975/1048576 : ℝ) ≤ (983941709969/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61496356873/62500000000 : ℝ) ≤ (radius 8 (16975/131072 : ℝ)) ∧ (radius 8 (16975/131072 : ℝ)) ≤ (983941709969/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16975/131072 : ℝ)) (61496356873/62500000000 : ℝ) (983941709969/1000000000000 : ℝ) (178490087633/1000000000000 : ℝ) (178490087639/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16975/131072 : ℝ)) (61496356873/62500000000 : ℝ) (983941709969/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61496356873/62500000000 : ℝ) (983941709969/1000000000000 : ℝ) (123996356873/125000000000 : ℝ) (198394170997/200000000000 : ℝ) (991938359963/1000000000000 : ℝ) (198387671993/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 1 (123996356873/125000000000 : ℝ) (198394170997/200000000000 : ℝ) (991938359963/1000000000000 : ℝ) (198387671993/200000000000 : ℝ) (991954607473/1000000000000 : ℝ) (39678184299/40000000000 : ℝ) (49597730367/50000000000 : ℝ) (495977303671/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 2 (991954607473/1000000000000 : ℝ) (39678184299/40000000000 : ℝ) (49597730367/50000000000 : ℝ) (495977303671/500000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 3 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 4 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 5 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 6 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16975/131072 : ℝ)) 7 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16975/131072 : ℝ))) (178490087633/1000000000000 : ℝ) (178490087639/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178490087633/1000000000000 : ℝ) (178490087639/1000000000000 : ℝ) (73655630477/125000000000 : ℝ) (29462252191/50000000000 : ℝ) (84496174501/200000000000 : ℝ) (422480872513/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 1 (73655630477/125000000000 : ℝ) (29462252191/50000000000 : ℝ) (84496174501/200000000000 : ℝ) (422480872513/1000000000000 : ℝ) (6323286977/12500000000 : ℝ) (505862958167/1000000000000 : ℝ) (498943644343/1000000000000 : ℝ) (9978872887/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 2 (6323286977/12500000000 : ℝ) (505862958167/1000000000000 : ℝ) (498943644343/1000000000000 : ℝ) (9978872887/20000000000 : ℝ) (502403301251/1000000000000 : ℝ) (502403301259/1000000000000 : ℝ) (25119569457/50000000000 : ℝ) (125597847287/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 3 (502403301251/1000000000000 : ℝ) (502403301259/1000000000000 : ℝ) (25119569457/50000000000 : ℝ) (125597847287/250000000000 : ℝ) (100479469039/200000000000 : ℝ) (125599336301/250000000000 : ℝ) (12559933629/25000000000 : ℝ) (502397345169/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 4 (100479469039/200000000000 : ℝ) (125599336301/250000000000 : ℝ) (12559933629/25000000000 : ℝ) (502397345169/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 5 (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 6 (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16975/131072 : ℝ))) 7 (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16975/131072 : ℝ)) hmem 8 (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16975/131072 : ℝ))) hcmem 8 (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16975/131072 : ℝ)) (495977303703/500000000000 : ℝ) (991954607409/1000000000000 : ℝ) (502397345177/1000000000000 : ℝ) (502397345187/1000000000000 : ℝ) (397782266699/500000000000 : ℝ) (795564533417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1455_exp_lower
  have heNumeric : (1027454094923/500000000000 : ℝ)/4 ≤ Real.exp (-10657011050297/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454094923/500000000000 : ℝ)/4 ≤ Real.exp ((8487/65536 : ℝ)-(795564533417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8487/65536 : ℝ) (16975/131072 : ℝ) (795564533417/1000000000000 : ℝ) (1027454094923/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1456; no trusted numerical premise.
theorem cover8_leaf1456_exp_radius : (997978349394563939/1000000000000000000 : ℝ) ≤ Real.exp ((-1061/65536 : ℝ)/8) ∧ Real.exp ((-1061/65536 : ℝ)/8) ≤ (49898917469728197/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1061/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1456_exp_lower : (115014228606276787/125000000000000000 : ℝ) ≤ Real.exp ((-4262803946573/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262803946573/6400000000000 : ℝ)/8) ≤ (920113828850214297/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262803946573/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1456_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727085473/250000000000 : ℝ) ≤ 4*Real.exp (16975/131072 : ℝ)*Real.exp (-mu (radius 8 (1061/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (513727085473/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1061/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1456_exp_radius
  have hrNumeric : (983940771609/1000000000000 : ℝ) ≤ Real.exp (-1061/65536 : ℝ) ∧ Real.exp (-1061/65536 : ℝ) ≤ (98394077161/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983940771609/1000000000000 : ℝ) ≤ (radius 8 (1061/8192 : ℝ)) ∧ (radius 8 (1061/8192 : ℝ)) ≤ (98394077161/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1061/8192 : ℝ)) (983940771609/1000000000000 : ℝ) (98394077161/100000000000 : ℝ) (178495260339/1000000000000 : ℝ) (35699052069/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1061/8192 : ℝ)) (983940771609/1000000000000 : ℝ) (98394077161/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983940771609/1000000000000 : ℝ) (98394077161/100000000000 : ℝ) (247992596451/250000000000 : ℝ) (198394077161/200000000000 : ℝ) (991937886971/1000000000000 : ℝ) (247984471743/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 1 (247992596451/250000000000 : ℝ) (198394077161/200000000000 : ℝ) (991937886971/1000000000000 : ℝ) (247984471743/250000000000 : ℝ) (991954136387/1000000000000 : ℝ) (991954136389/1000000000000 : ℝ) (495977068127/500000000000 : ℝ) (15499283379/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 2 (991954136387/1000000000000 : ℝ) (991954136389/1000000000000 : ℝ) (495977068127/500000000000 : ℝ) (15499283379/15625000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 3 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 4 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 5 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 6 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1061/8192 : ℝ)) 7 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1061/8192 : ℝ))) (178495260339/1000000000000 : ℝ) (35699052069/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178495260339/1000000000000 : ℝ) (35699052069/200000000000 : ℝ) (589247630169/1000000000000 : ℝ) (589247630173/1000000000000 : ℝ) (422486994283/1000000000000 : ℝ) (422486994291/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 1 (589247630169/1000000000000 : ℝ) (589247630173/1000000000000 : ℝ) (422486994283/1000000000000 : ℝ) (422486994291/1000000000000 : ℝ) (252933656113/500000000000 : ℝ) (63233414029/125000000000 : ℝ) (498948354199/1000000000000 : ℝ) (498948354207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 2 (252933656113/500000000000 : ℝ) (63233414029/125000000000 : ℝ) (498948354199/1000000000000 : ℝ) (498948354207/1000000000000 : ℝ) (125601958303/250000000000 : ℝ) (25120391661/50000000000 : ℝ) (502395922433/1000000000000 : ℝ) (502395922441/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 3 (125601958303/250000000000 : ℝ) (25120391661/50000000000 : ℝ) (502395922433/1000000000000 : ℝ) (502395922441/1000000000000 : ℝ) (251200938911/500000000000 : ℝ) (502401877831/1000000000000 : ℝ) (502401877787/1000000000000 : ℝ) (125600469449/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 4 (251200938911/500000000000 : ℝ) (502401877831/1000000000000 : ℝ) (502401877787/1000000000000 : ℝ) (125600469449/250000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 5 (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 6 (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1061/8192 : ℝ))) 7 (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1061/8192 : ℝ)) hmem 8 (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1061/8192 : ℝ))) hcmem 8 (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1061/8192 : ℝ)) (774964169/781250000 : ℝ) (991954136323/1000000000000 : ℝ) (125600469451/250000000000 : ℝ) (251200938907/500000000000 : ℝ) (795572088801/1000000000000 : ℝ) (39778604441/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1456_exp_lower
  have heNumeric : (513727085473/250000000000 : ℝ)/4 ≤ Real.exp (-4262803946573/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727085473/250000000000 : ℝ)/4 ≤ Real.exp ((16975/131072 : ℝ)-(39778604441/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16975/131072 : ℝ) (1061/8192 : ℝ) (39778604441/50000000000 : ℝ) (513727085473/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1457; no trusted numerical premise.
theorem cover8_leaf1457_exp_radius : (997978230426281011/1000000000000000000 : ℝ) ≤ Real.exp ((-16977/1048576 : ℝ)/8) ∧ Real.exp ((-16977/1048576 : ℝ)/8) ≤ (249494557606570253/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16977/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1457_exp_lower : (920113837394337437/1000000000000000000 : ℝ) ≤ Real.exp ((-1332126084729/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332126084729/2000000000000 : ℝ)/8) ≤ (460056918697168719/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332126084729/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1457_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454247273/500000000000 : ℝ) ≤ 4*Real.exp (1061/8192 : ℝ)*Real.exp (-mu (radius 8 (16977/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454247273/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16977/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1457_exp_radius
  have hrNumeric : (3935759333/4000000000 : ℝ) ≤ Real.exp (-16977/1048576 : ℝ) ∧ Real.exp (-16977/1048576 : ℝ) ≤ (983939833251/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3935759333/4000000000 : ℝ) ≤ (radius 8 (16977/131072 : ℝ)) ∧ (radius 8 (16977/131072 : ℝ)) ≤ (983939833251/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16977/131072 : ℝ)) (3935759333/4000000000 : ℝ) (983939833251/1000000000000 : ℝ) (17850043289/100000000000 : ℝ) (174316829/976562500 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16977/131072 : ℝ)) (3935759333/4000000000 : ℝ) (983939833251/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3935759333/4000000000 : ℝ) (983939833251/1000000000000 : ℝ) (7935759333/8000000000 : ℝ) (495984958313/500000000000 : ℝ) (495968706989/500000000000 : ℝ) (991937413979/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 1 (7935759333/8000000000 : ℝ) (495984958313/500000000000 : ℝ) (495968706989/500000000000 : ℝ) (991937413979/1000000000000 : ℝ) (991953665301/1000000000000 : ℝ) (991953665303/1000000000000 : ℝ) (61997104073/62500000000 : ℝ) (99195366517/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 2 (991953665301/1000000000000 : ℝ) (991953665303/1000000000000 : ℝ) (61997104073/62500000000 : ℝ) (99195366517/100000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 3 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 4 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 5 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 6 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16977/131072 : ℝ)) 7 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16977/131072 : ℝ))) (17850043289/100000000000 : ℝ) (174316829/976562500 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17850043289/100000000000 : ℝ) (174316829/976562500 : ℝ) (117850043289/200000000000 : ℝ) (1150879329/1953125000 : ℝ) (42249311579/100000000000 : ℝ) (211246557899/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 1 (117850043289/200000000000 : ℝ) (1150879329/1953125000 : ℝ) (42249311579/100000000000 : ℝ) (211246557899/500000000000 : ℝ) (505871666117/1000000000000 : ℝ) (505871666123/1000000000000 : ℝ) (9979061277/20000000000 : ℝ) (498953063857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 2 (505871666117/1000000000000 : ℝ) (505871666123/1000000000000 : ℝ) (9979061277/20000000000 : ℝ) (498953063857/1000000000000 : ℝ) (502412364983/1000000000000 : ℝ) (50241236499/100000000000 : ℝ) (502400455537/1000000000000 : ℝ) (62800056943/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 3 (502412364983/1000000000000 : ℝ) (50241236499/100000000000 : ℝ) (502400455537/1000000000000 : ℝ) (62800056943/125000000000 : ℝ) (25120320513/50000000000 : ℝ) (502406410267/1000000000000 : ℝ) (31400400639/62500000000 : ℝ) (62800801279/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 4 (25120320513/50000000000 : ℝ) (502406410267/1000000000000 : ℝ) (31400400639/62500000000 : ℝ) (62800801279/125000000000 : ℝ) (251203205121/500000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 5 (251203205121/500000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 6 (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16977/131072 : ℝ))) 7 (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16977/131072 : ℝ)) hmem 8 (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16977/131072 : ℝ))) hcmem 8 (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16977/131072 : ℝ)) (495976832617/500000000000 : ℝ) (991953665237/1000000000000 : ℝ) (502406410241/1000000000000 : ℝ) (2009625641/4000000000 : ℝ) (79557964391/100000000000 : ℝ) (795579643927/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1457_exp_lower
  have heNumeric : (1027454247273/500000000000 : ℝ)/4 ≤ Real.exp (-1332126084729/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454247273/500000000000 : ℝ)/4 ≤ Real.exp ((1061/8192 : ℝ)-(795579643927/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1061/8192 : ℝ) (16977/131072 : ℝ) (795579643927/1000000000000 : ℝ) (1027454247273/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1458; no trusted numerical premise.
theorem cover8_leaf1458_exp_radius : (498989055729006133/500000000000000000 : ℝ) ≤ Real.exp ((-8489/524288 : ℝ)/8) ∧ Real.exp ((-8489/524288 : ℝ)/8) ≤ (997978111458012267/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8489/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1458_exp_lower : (460056922986769999/500000000000000000 : ℝ) ≤ Real.exp ((-21314014968703/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314014968703/32000000000000 : ℝ)/8) ≤ (920113845973539999/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314014968703/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1458_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454323913/500000000000 : ℝ) ≤ 4*Real.exp (16977/131072 : ℝ)*Real.exp (-mu (radius 8 (8489/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454323913/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8489/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1458_exp_radius
  have hrNumeric : (983938894893/1000000000000 : ℝ) ≤ Real.exp (-8489/524288 : ℝ) ∧ Real.exp (-8489/524288 : ℝ) ≤ (491969447447/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983938894893/1000000000000 : ℝ) ≤ (radius 8 (8489/65536 : ℝ)) ∧ (radius 8 (8489/65536 : ℝ)) ≤ (491969447447/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8489/65536 : ℝ)) (983938894893/1000000000000 : ℝ) (491969447447/500000000000 : ℝ) (7140224211/40000000000 : ℝ) (89252802641/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8489/65536 : ℝ)) (983938894893/1000000000000 : ℝ) (491969447447/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983938894893/1000000000000 : ℝ) (491969447447/500000000000 : ℝ) (495984723723/500000000000 : ℝ) (991969447447/1000000000000 : ℝ) (495968470493/500000000000 : ℝ) (991936940987/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 1 (495984723723/500000000000 : ℝ) (991969447447/1000000000000 : ℝ) (495968470493/500000000000 : ℝ) (991936940987/1000000000000 : ℝ) (123994149277/125000000000 : ℝ) (991953194217/1000000000000 : ℝ) (495976597041/500000000000 : ℝ) (247988298521/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 2 (123994149277/125000000000 : ℝ) (991953194217/1000000000000 : ℝ) (495976597041/500000000000 : ℝ) (247988298521/250000000000 : ℝ) (991953194149/1000000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 3 (991953194149/1000000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 4 (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 5 (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 6 (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8489/65536 : ℝ)) 7 (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8489/65536 : ℝ))) (7140224211/40000000000 : ℝ) (89252802641/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7140224211/40000000000 : ℝ) (89252802641/500000000000 : ℝ) (589252802637/1000000000000 : ℝ) (589252802641/1000000000000 : ℝ) (422499237011/1000000000000 : ℝ) (21124961851/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 1 (589252802637/1000000000000 : ℝ) (589252802641/1000000000000 : ℝ) (422499237011/1000000000000 : ℝ) (21124961851/50000000000 : ℝ) (31617251239/62500000000 : ℝ) (505876019831/1000000000000 : ℝ) (124739443321/250000000000 : ℝ) (124739443323/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 2 (31617251239/62500000000 : ℝ) (505876019831/1000000000000 : ℝ) (124739443321/250000000000 : ℝ) (124739443323/250000000000 : ℝ) (251208448277/500000000000 : ℝ) (251208448281/500000000000 : ℝ) (502404988439/1000000000000 : ℝ) (15700155889/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 3 (251208448277/500000000000 : ℝ) (251208448281/500000000000 : ℝ) (502404988439/1000000000000 : ℝ) (15700155889/31250000000 : ℝ) (15700341953/31250000000 : ℝ) (100482188501/200000000000 : ℝ) (502410942461/1000000000000 : ℝ) (50241094247/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 4 (15700341953/31250000000 : ℝ) (100482188501/200000000000 : ℝ) (502410942461/1000000000000 : ℝ) (50241094247/100000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 5 (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 6 (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8489/65536 : ℝ))) 7 (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8489/65536 : ℝ)) hmem 8 (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8489/65536 : ℝ))) hcmem 8 (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8489/65536 : ℝ)) (247988298537/250000000000 : ℝ) (991953194151/1000000000000 : ℝ) (251205471239/500000000000 : ℝ) (62801367811/125000000000 : ℝ) (795587198709/1000000000000 : ℝ) (795587198729/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1458_exp_lower
  have heNumeric : (1027454323913/500000000000 : ℝ)/4 ≤ Real.exp (-21314014968703/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454323913/500000000000 : ℝ)/4 ≤ Real.exp ((16977/131072 : ℝ)-(795587198729/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16977/131072 : ℝ) (8489/65536 : ℝ) (795587198729/1000000000000 : ℝ) (1027454323913/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1459; no trusted numerical premise.
theorem cover8_leaf1459_exp_radius : (997977992489757703/1000000000000000000 : ℝ) ≤ Real.exp ((-16979/1048576 : ℝ)/8) ∧ Real.exp ((-16979/1048576 : ℝ)/8) ≤ (124747249061219713/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16979/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1459_exp_lower : (920113854587246909/1000000000000000000 : ℝ) ≤ Real.exp ((-10657006286071/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657006286071/16000000000000 : ℝ)/8) ≤ (92011385458724691/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657006286071/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1459_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727200431/250000000000 : ℝ) ≤ 4*Real.exp (8489/65536 : ℝ)*Real.exp (-mu (radius 8 (16979/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513727200431/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16979/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1459_exp_radius
  have hrNumeric : (122992244567/125000000000 : ℝ) ≤ Real.exp (-16979/1048576 : ℝ) ∧ Real.exp (-16979/1048576 : ℝ) ≤ (983937956537/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122992244567/125000000000 : ℝ) ≤ (radius 8 (16979/131072 : ℝ)) ∧ (radius 8 (16979/131072 : ℝ)) ≤ (983937956537/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16979/131072 : ℝ)) (122992244567/125000000000 : ℝ) (983937956537/1000000000000 : ℝ) (35702155501/200000000000 : ℝ) (22313847189/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16979/131072 : ℝ)) (122992244567/125000000000 : ℝ) (983937956537/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122992244567/125000000000 : ℝ) (983937956537/1000000000000 : ℝ) (247992244567/250000000000 : ℝ) (991968978269/1000000000000 : ℝ) (991936467993/1000000000000 : ℝ) (198387293599/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 1 (247992244567/250000000000 : ℝ) (991968978269/1000000000000 : ℝ) (991936467993/1000000000000 : ℝ) (198387293599/200000000000 : ℝ) (99195272313/100000000000 : ℝ) (247988180783/250000000000 : ℝ) (991952722997/1000000000000 : ℝ) (991952722999/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 2 (99195272313/100000000000 : ℝ) (247988180783/250000000000 : ℝ) (991952722997/1000000000000 : ℝ) (991952722999/1000000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 3 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 4 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 5 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 6 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16979/131072 : ℝ)) 7 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16979/131072 : ℝ))) (35702155501/200000000000 : ℝ) (22313847189/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35702155501/200000000000 : ℝ) (22313847189/125000000000 : ℝ) (36828461797/62500000000 : ℝ) (147313847189/250000000000 : ℝ) (10562633949/25000000000 : ℝ) (422505357969/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 1 (36828461797/62500000000 : ℝ) (147313847189/250000000000 : ℝ) (10562633949/25000000000 : ℝ) (422505357969/1000000000000 : ℝ) (126470093339/250000000000 : ℝ) (505880373363/1000000000000 : ℝ) (498962482511/1000000000000 : ℝ) (498962482519/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 2 (126470093339/250000000000 : ℝ) (505880373363/1000000000000 : ℝ) (498962482511/1000000000000 : ℝ) (498962482519/1000000000000 : ℝ) (502421427933/1000000000000 : ℝ) (502421427941/1000000000000 : ℝ) (502409521151/1000000000000 : ℝ) (502409521159/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 3 (502421427933/1000000000000 : ℝ) (502421427941/1000000000000 : ℝ) (502409521151/1000000000000 : ℝ) (502409521159/1000000000000 : ℝ) (251207737271/500000000000 : ℝ) (10048309491/20000000000 : ℝ) (251207737253/500000000000 : ℝ) (100483094903/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 4 (251207737271/500000000000 : ℝ) (10048309491/20000000000 : ℝ) (251207737253/500000000000 : ℝ) (100483094903/200000000000 : ℝ) (125603868631/250000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 5 (125603868631/250000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 6 (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16979/131072 : ℝ))) 7 (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16979/131072 : ℝ)) hmem 8 (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16979/131072 : ℝ))) hcmem 8 (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16979/131072 : ℝ)) (991952723063/1000000000000 : ℝ) (495976361533/500000000000 : ℝ) (502415474523/1000000000000 : ℝ) (502415474533/1000000000000 : ℝ) (795594753211/1000000000000 : ℝ) (795594753231/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1459_exp_lower
  have heNumeric : (513727200431/250000000000 : ℝ)/4 ≤ Real.exp (-10657006286071/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727200431/250000000000 : ℝ)/4 ≤ Real.exp ((8489/65536 : ℝ)-(795594753231/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8489/65536 : ℝ) (16979/131072 : ℝ) (795594753231/1000000000000 : ℝ) (513727200431/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1460; no trusted numerical premise.
theorem cover8_leaf1460_exp_radius : (498988936760758661/500000000000000000 : ℝ) ≤ Real.exp ((-4245/262144 : ℝ)/8) ∧ Real.exp ((-4245/262144 : ℝ)/8) ≤ (997977873521517323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4245/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1460_exp_lower : (230028465808835789/250000000000000000 : ℝ) ≤ Real.exp ((-21314010166013/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314010166013/32000000000000 : ℝ)/8) ≤ (920113863235343157/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314010166013/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1460_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727239059/250000000000 : ℝ) ≤ 4*Real.exp (16979/131072 : ℝ)*Real.exp (-mu (radius 8 (4245/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513727239059/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4245/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1460_exp_radius
  have hrNumeric : (49196850909/50000000000 : ℝ) ≤ Real.exp (-4245/262144 : ℝ) ∧ Real.exp (-4245/262144 : ℝ) ≤ (983937018181/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49196850909/50000000000 : ℝ) ≤ (radius 8 (4245/32768 : ℝ)) ∧ (radius 8 (4245/32768 : ℝ)) ≤ (983937018181/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4245/32768 : ℝ)) (49196850909/50000000000 : ℝ) (983937018181/1000000000000 : ℝ) (22314493697/125000000000 : ℝ) (89257974791/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4245/32768 : ℝ)) (49196850909/50000000000 : ℝ) (983937018181/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49196850909/50000000000 : ℝ) (983937018181/1000000000000 : ℝ) (99196850909/100000000000 : ℝ) (991968509091/1000000000000 : ℝ) (991935995001/1000000000000 : ℝ) (991935995003/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 1 (99196850909/100000000000 : ℝ) (991968509091/1000000000000 : ℝ) (991935995001/1000000000000 : ℝ) (991935995003/1000000000000 : ℝ) (198390450409/200000000000 : ℝ) (991952252047/1000000000000 : ℝ) (123994031489/125000000000 : ℝ) (495976125957/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 2 (198390450409/200000000000 : ℝ) (991952252047/1000000000000 : ℝ) (123994031489/125000000000 : ℝ) (495976125957/500000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 3 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 4 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 5 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 6 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4245/32768 : ℝ)) 7 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4245/32768 : ℝ))) (22314493697/125000000000 : ℝ) (89257974791/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22314493697/125000000000 : ℝ) (89257974791/500000000000 : ℝ) (147314493697/250000000000 : ℝ) (589257974791/1000000000000 : ℝ) (52813934829/125000000000 : ℝ) (5281393483/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 1 (147314493697/250000000000 : ℝ) (589257974791/1000000000000 : ℝ) (52813934829/125000000000 : ℝ) (5281393483/12500000000 : ℝ) (50588472671/100000000000 : ℝ) (126471181679/250000000000 : ℝ) (49896719153/100000000000 : ℝ) (498967191537/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 2 (50588472671/100000000000 : ℝ) (126471181679/250000000000 : ℝ) (49896719153/100000000000 : ℝ) (498967191537/1000000000000 : ℝ) (6280324489/12500000000 : ℝ) (502425959127/1000000000000 : ℝ) (502414053669/1000000000000 : ℝ) (125603513419/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 3 (6280324489/12500000000 : ℝ) (502425959127/1000000000000 : ℝ) (502414053669/1000000000000 : ℝ) (125603513419/250000000000 : ℝ) (251210003197/500000000000 : ℝ) (251210003201/500000000000 : ℝ) (502420006359/1000000000000 : ℝ) (502420006367/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 4 (251210003197/500000000000 : ℝ) (251210003201/500000000000 : ℝ) (502420006359/1000000000000 : ℝ) (502420006367/1000000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 5 (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 6 (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4245/32768 : ℝ))) 7 (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4245/32768 : ℝ)) hmem 8 (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4245/32768 : ℝ))) hcmem 8 (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4245/32768 : ℝ)) (495976125989/500000000000 : ℝ) (991952251981/1000000000000 : ℝ) (62802500797/125000000000 : ℝ) (100484001277/200000000000 : ℝ) (795602307417/1000000000000 : ℝ) (397801153717/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1460_exp_lower
  have heNumeric : (513727239059/250000000000 : ℝ)/4 ≤ Real.exp (-21314010166013/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727239059/250000000000 : ℝ)/4 ≤ Real.exp ((16979/131072 : ℝ)-(397801153717/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16979/131072 : ℝ) (4245/32768 : ℝ) (397801153717/500000000000 : ℝ) (513727239059/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1461; no trusted numerical premise.
theorem cover8_leaf1461_exp_radius : (997977754553291123/1000000000000000000 : ℝ) ≤ Real.exp ((-16981/1048576 : ℝ)/8) ∧ Real.exp ((-16981/1048576 : ℝ)/8) ≤ (249494438638322781/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16981/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1461_exp_lower : (920113871918173783/1000000000000000000 : ℝ) ≤ Real.exp ((-1065700387511/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065700387511/1600000000000 : ℝ)/8) ≤ (115014233989771723/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065700387511/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1461_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863638921/125000000000 : ℝ) ≤ 4*Real.exp (4245/32768 : ℝ)*Real.exp (-mu (radius 8 (16981/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256863638921/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16981/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1461_exp_radius
  have hrNumeric : (39357443193/40000000000 : ℝ) ≤ Real.exp (-16981/1048576 : ℝ) ∧ Real.exp (-16981/1048576 : ℝ) ≤ (491968039913/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39357443193/40000000000 : ℝ) ≤ (radius 8 (16981/131072 : ℝ)) ∧ (radius 8 (16981/131072 : ℝ)) ≤ (491968039913/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16981/131072 : ℝ)) (39357443193/40000000000 : ℝ) (491968039913/500000000000 : ℝ) (89260560743/500000000000 : ℝ) (44630280373/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16981/131072 : ℝ)) (39357443193/40000000000 : ℝ) (491968039913/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39357443193/40000000000 : ℝ) (491968039913/500000000000 : ℝ) (123996004989/125000000000 : ℝ) (991968039913/1000000000000 : ℝ) (991935522009/1000000000000 : ℝ) (991935522011/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 1 (123996004989/125000000000 : ℝ) (991968039913/1000000000000 : ℝ) (991935522009/1000000000000 : ℝ) (991935522011/1000000000000 : ℝ) (6199698631/6250000000 : ℝ) (495975890481/500000000000 : ℝ) (991951780827/1000000000000 : ℝ) (991951780829/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 2 (6199698631/6250000000 : ℝ) (495975890481/500000000000 : ℝ) (991951780827/1000000000000 : ℝ) (991951780829/1000000000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 3 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 4 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 5 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 6 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16981/131072 : ℝ)) 7 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16981/131072 : ℝ))) (89260560743/500000000000 : ℝ) (44630280373/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89260560743/500000000000 : ℝ) (44630280373/250000000000 : ℝ) (589260560743/1000000000000 : ℝ) (294630280373/500000000000 : ℝ) (16900703961/40000000000 : ℝ) (422517599033/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 1 (589260560743/1000000000000 : ℝ) (294630280373/500000000000 : ℝ) (16900703961/40000000000 : ℝ) (422517599033/1000000000000 : ℝ) (126472269971/250000000000 : ℝ) (50588907989/100000000000 : ℝ) (31185743771/62500000000 : ℝ) (498971900343/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 2 (126472269971/250000000000 : ℝ) (50588907989/100000000000 : ℝ) (31185743771/62500000000 : ℝ) (498971900343/1000000000000 : ℝ) (50243049011/100000000000 : ℝ) (502430490117/1000000000000 : ℝ) (50241858599/100000000000 : ℝ) (251209292999/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 3 (50243049011/100000000000 : ℝ) (502430490117/1000000000000 : ℝ) (50241858599/100000000000 : ℝ) (251209292999/500000000000 : ℝ) (10048490761/20000000000 : ℝ) (251212269029/500000000000 : ℝ) (251212269007/500000000000 : ℝ) (502424538023/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 4 (10048490761/20000000000 : ℝ) (251212269029/500000000000 : ℝ) (251212269007/500000000000 : ℝ) (502424538023/1000000000000 : ℝ) (31401533627/62500000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 5 (31401533627/62500000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 6 (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16981/131072 : ℝ))) 7 (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16981/131072 : ℝ)) hmem 8 (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16981/131072 : ℝ))) hcmem 8 (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16981/131072 : ℝ)) (991951780893/1000000000000 : ℝ) (30998493153/31250000000 : ℝ) (502424538031/1000000000000 : ℝ) (502424538041/1000000000000 : ℝ) (159121972263/200000000000 : ℝ) (159121972267/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1461_exp_lower
  have heNumeric : (256863638921/125000000000 : ℝ)/4 ≤ Real.exp (-1065700387511/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863638921/125000000000 : ℝ)/4 ≤ Real.exp ((4245/32768 : ℝ)-(159121972267/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4245/32768 : ℝ) (16981/131072 : ℝ) (159121972267/200000000000 : ℝ) (256863638921/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1462; no trusted numerical premise.
theorem cover8_leaf1462_exp_radius : (997977635585079107/1000000000000000000 : ℝ) ≤ Real.exp ((-8491/524288 : ℝ)/8) ∧ Real.exp ((-8491/524288 : ℝ)/8) ≤ (249494408896269777/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8491/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1462_exp_lower : (920113880636083833/1000000000000000000 : ℝ) ≤ Real.exp ((-21314005324667/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314005324667/32000000000000 : ℝ)/8) ≤ (460056940318041917/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314005324667/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1462_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909267127/1000000000000 : ℝ) ≤ 4*Real.exp (16981/131072 : ℝ)*Real.exp (-mu (radius 8 (8491/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909267127/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8491/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1462_exp_radius
  have hrNumeric : (983935141471/1000000000000 : ℝ) ≤ Real.exp (-8491/524288 : ℝ) ∧ Real.exp (-8491/524288 : ℝ) ≤ (30747973171/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983935141471/1000000000000 : ℝ) ≤ (radius 8 (8491/65536 : ℝ)) ∧ (radius 8 (8491/65536 : ℝ)) ≤ (30747973171/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8491/65536 : ℝ)) (983935141471/1000000000000 : ℝ) (30747973171/31250000000 : ℝ) (35705258647/200000000000 : ℝ) (89263146621/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8491/65536 : ℝ)) (983935141471/1000000000000 : ℝ) (30747973171/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983935141471/1000000000000 : ℝ) (30747973171/31250000000 : ℝ) (198393514147/200000000000 : ℝ) (61997973171/62500000000 : ℝ) (495967524509/500000000000 : ℝ) (991935049019/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 1 (198393514147/200000000000 : ℝ) (61997973171/62500000000 : ℝ) (495967524509/500000000000 : ℝ) (991935049019/1000000000000 : ℝ) (247987827469/250000000000 : ℝ) (495975654939/500000000000 : ℝ) (991951309743/1000000000000 : ℝ) (198390261949/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 2 (247987827469/250000000000 : ℝ) (495975654939/500000000000 : ℝ) (991951309743/1000000000000 : ℝ) (198390261949/200000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 3 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 4 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 5 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 6 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8491/65536 : ℝ)) 7 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8491/65536 : ℝ))) (35705258647/200000000000 : ℝ) (89263146621/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35705258647/200000000000 : ℝ) (89263146621/500000000000 : ℝ) (589263146617/1000000000000 : ℝ) (589263146621/1000000000000 : ℝ) (211261859569/500000000000 : ℝ) (105630929787/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 1 (589263146617/1000000000000 : ℝ) (589263146621/1000000000000 : ℝ) (211261859569/500000000000 : ℝ) (105630929787/250000000000 : ℝ) (505893432877/1000000000000 : ℝ) (101178686577/200000000000 : ℝ) (49897660893/100000000000 : ℝ) (249488304469/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 2 (505893432877/1000000000000 : ℝ) (101178686577/200000000000 : ℝ) (49897660893/100000000000 : ℝ) (249488304469/500000000000 : ℝ) (502435020903/1000000000000 : ℝ) (31402188807/62500000000 : ℝ) (100484623623/200000000000 : ℝ) (125605779531/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 3 (502435020903/1000000000000 : ℝ) (31402188807/62500000000 : ℝ) (100484623623/200000000000 : ℝ) (125605779531/250000000000 : ℝ) (502429069509/1000000000000 : ℝ) (251214534759/500000000000 : ℝ) (502429069473/1000000000000 : ℝ) (502429069483/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 4 (502429069509/1000000000000 : ℝ) (251214534759/500000000000 : ℝ) (502429069473/1000000000000 : ℝ) (502429069483/1000000000000 : ℝ) (502429069491/1000000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 5 (502429069491/1000000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 6 (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8491/65536 : ℝ))) 7 (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8491/65536 : ℝ)) hmem 8 (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8491/65536 : ℝ))) hcmem 8 (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8491/65536 : ℝ)) (991951309809/1000000000000 : ℝ) (247987827453/250000000000 : ℝ) (50242906949/100000000000 : ℝ) (502429069501/1000000000000 : ℝ) (79561741491/100000000000 : ℝ) (795617414931/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1462_exp_lower
  have heNumeric : (2054909267127/1000000000000 : ℝ)/4 ≤ Real.exp (-21314005324667/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909267127/1000000000000 : ℝ)/4 ≤ Real.exp ((16981/131072 : ℝ)-(795617414931/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16981/131072 : ℝ) (8491/65536 : ℝ) (795617414931/1000000000000 : ℝ) (2054909267127/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1463; no trusted numerical premise.
theorem cover8_leaf1463_exp_radius : (124747189577110159/125000000000000000 : ℝ) ≤ Real.exp ((-16983/1048576 : ℝ)/8) ∧ Real.exp ((-16983/1048576 : ℝ)/8) ≤ (997977516616881273/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16983/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1463_exp_lower : (920113889388498237/1000000000000000000 : ℝ) ≤ Real.exp ((-10657001444757/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657001444757/16000000000000 : ℝ)/8) ≤ (460056944694249119/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657001444757/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1463_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909423503/1000000000000 : ℝ) ≤ 4*Real.exp (8491/65536 : ℝ)*Real.exp (-mu (radius 8 (16983/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909423503/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16983/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1463_exp_radius
  have hrNumeric : (491967101559/500000000000 : ℝ) ≤ Real.exp (-16983/1048576 : ℝ) ∧ Real.exp (-16983/1048576 : ℝ) ≤ (983934203119/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491967101559/500000000000 : ℝ) ≤ (radius 8 (16983/131072 : ℝ)) ∧ (radius 8 (16983/131072 : ℝ)) ≤ (983934203119/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16983/131072 : ℝ)) (491967101559/500000000000 : ℝ) (983934203119/1000000000000 : ℝ) (7141258593/40000000000 : ℝ) (178531464831/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16983/131072 : ℝ)) (491967101559/500000000000 : ℝ) (983934203119/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491967101559/500000000000 : ℝ) (983934203119/1000000000000 : ℝ) (991967101559/1000000000000 : ℝ) (24799177539/25000000000 : ℝ) (991934576027/1000000000000 : ℝ) (247983644007/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 1 (991967101559/1000000000000 : ℝ) (24799177539/25000000000 : ℝ) (991934576027/1000000000000 : ℝ) (247983644007/250000000000 : ℝ) (991950838793/1000000000000 : ℝ) (495975419397/500000000000 : ℝ) (991950838659/1000000000000 : ℝ) (991950838661/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 2 (991950838793/1000000000000 : ℝ) (495975419397/500000000000 : ℝ) (991950838659/1000000000000 : ℝ) (991950838661/1000000000000 : ℝ) (495975419363/500000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 3 (495975419363/500000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 4 (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 5 (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 6 (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16983/131072 : ℝ)) 7 (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16983/131072 : ℝ))) (7141258593/40000000000 : ℝ) (178531464831/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7141258593/40000000000 : ℝ) (178531464831/1000000000000 : ℝ) (147316433103/250000000000 : ℝ) (9207277069/15625000000 : ℝ) (16901193559/40000000000 : ℝ) (52816229873/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 1 (147316433103/250000000000 : ℝ) (9207277069/15625000000 : ℝ) (16901193559/40000000000 : ℝ) (52816229873/125000000000 : ℝ) (505897785693/1000000000000 : ℝ) (5058977857/10000000000 : ℝ) (99796263463/200000000000 : ℝ) (498981317323/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 2 (505897785693/1000000000000 : ℝ) (5058977857/10000000000 : ℝ) (99796263463/200000000000 : ℝ) (498981317323/1000000000000 : ℝ) (31402471969/62500000000 : ℝ) (62804943939/125000000000 : ℝ) (502427650047/1000000000000 : ℝ) (100485530011/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 3 (31402471969/62500000000 : ℝ) (62804943939/125000000000 : ℝ) (502427650047/1000000000000 : ℝ) (100485530011/200000000000 : ℝ) (20097344031/40000000000 : ℝ) (31402100049/62500000000 : ℝ) (25121680037/50000000000 : ℝ) (502433600749/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 4 (20097344031/40000000000 : ℝ) (31402100049/62500000000 : ℝ) (25121680037/50000000000 : ℝ) (502433600749/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 5 (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 6 (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16983/131072 : ℝ))) 7 (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16983/131072 : ℝ)) hmem 8 (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16983/131072 : ℝ))) hcmem 8 (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16983/131072 : ℝ)) (39678033549/40000000000 : ℝ) (123993854841/125000000000 : ℝ) (502433600757/1000000000000 : ℝ) (502433600767/1000000000000 : ℝ) (49726560513/62500000000 : ℝ) (795624968227/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1463_exp_lower
  have heNumeric : (2054909423503/1000000000000 : ℝ)/4 ≤ Real.exp (-10657001444757/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909423503/1000000000000 : ℝ)/4 ≤ Real.exp ((8491/65536 : ℝ)-(795624968227/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8491/65536 : ℝ) (16983/131072 : ℝ) (795624968227/1000000000000 : ℝ) (2054909423503/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1464; no trusted numerical premise.
theorem cover8_leaf1464_exp_radius : (49898869882434881/50000000000000000 : ℝ) ≤ Real.exp ((-2123/131072 : ℝ)/8) ∧ Real.exp ((-2123/131072 : ℝ)/8) ≤ (997977397648697621/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2123/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1464_exp_lower : (920113898174956939/1000000000000000000 : ℝ) ≤ Real.exp ((-21314000444889/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314000444889/32000000000000 : ℝ)/8) ≤ (46005694908747847/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314000444889/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1464_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454790243/500000000000 : ℝ) ≤ 4*Real.exp (16983/131072 : ℝ)*Real.exp (-mu (radius 8 (2123/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454790243/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2123/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1464_exp_radius
  have hrNumeric : (196786652953/200000000000 : ℝ) ≤ Real.exp (-2123/131072 : ℝ) ∧ Real.exp (-2123/131072 : ℝ) ≤ (491966632383/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196786652953/200000000000 : ℝ) ≤ (radius 8 (2123/16384 : ℝ)) ∧ (radius 8 (2123/16384 : ℝ)) ≤ (491966632383/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2123/16384 : ℝ)) (196786652953/200000000000 : ℝ) (491966632383/500000000000 : ℝ) (178536636259/1000000000000 : ℝ) (89268318133/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2123/16384 : ℝ)) (196786652953/200000000000 : ℝ) (491966632383/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196786652953/200000000000 : ℝ) (491966632383/500000000000 : ℝ) (495983316191/500000000000 : ℝ) (991966632383/1000000000000 : ℝ) (198386820607/200000000000 : ℝ) (991934103037/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 1 (495983316191/500000000000 : ℝ) (991966632383/1000000000000 : ℝ) (198386820607/200000000000 : ℝ) (991934103037/1000000000000 : ℝ) (247987591927/250000000000 : ℝ) (99195036771/100000000000 : ℝ) (39678014703/40000000000 : ℝ) (991950367577/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 2 (247987591927/250000000000 : ℝ) (99195036771/100000000000 : ℝ) (39678014703/40000000000 : ℝ) (991950367577/1000000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 3 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 4 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 5 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 6 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2123/16384 : ℝ)) 7 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2123/16384 : ℝ))) (178536636259/1000000000000 : ℝ) (89268318133/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178536636259/1000000000000 : ℝ) (89268318133/500000000000 : ℝ) (589268318129/1000000000000 : ℝ) (589268318133/1000000000000 : ℝ) (422535958539/1000000000000 : ℝ) (105633989637/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 1 (589268318129/1000000000000 : ℝ) (589268318133/1000000000000 : ℝ) (422535958539/1000000000000 : ℝ) (105633989637/250000000000 : ℝ) (252951069167/500000000000 : ℝ) (505902138341/1000000000000 : ℝ) (498986025493/1000000000000 : ℝ) (498986025501/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 2 (252951069167/500000000000 : ℝ) (505902138341/1000000000000 : ℝ) (498986025493/1000000000000 : ℝ) (498986025501/1000000000000 : ℝ) (502444081913/1000000000000 : ℝ) (502444081921/1000000000000 : ℝ) (502432181787/1000000000000 : ℝ) (100486436359/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 3 (502444081913/1000000000000 : ℝ) (502444081921/1000000000000 : ℝ) (502432181787/1000000000000 : ℝ) (100486436359/200000000000 : ℝ) (10048762637/20000000000 : ℝ) (251219065929/500000000000 : ℝ) (251219065907/500000000000 : ℝ) (502438131823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 4 (10048762637/20000000000 : ℝ) (251219065929/500000000000 : ℝ) (251219065907/500000000000 : ℝ) (502438131823/1000000000000 : ℝ) (62804766479/125000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 5 (62804766479/125000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 6 (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2123/16384 : ℝ))) 7 (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2123/16384 : ℝ)) hmem 8 (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2123/16384 : ℝ))) hcmem 8 (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2123/16384 : ℝ)) (991950367641/1000000000000 : ℝ) (247987591911/250000000000 : ℝ) (502438131831/1000000000000 : ℝ) (502438131841/1000000000000 : ℝ) (99454065151/125000000000 : ℝ) (795632521227/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1464_exp_lower
  have heNumeric : (1027454790243/500000000000 : ℝ)/4 ≤ Real.exp (-21314000444889/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454790243/500000000000 : ℝ)/4 ≤ Real.exp ((16983/131072 : ℝ)-(795632521227/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16983/131072 : ℝ) (2123/16384 : ℝ) (795632521227/1000000000000 : ℝ) (1027454790243/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1465; no trusted numerical premise.
theorem cover8_leaf1465_exp_radius : (997977278680528149/1000000000000000000 : ℝ) ≤ Real.exp ((-16985/1048576 : ℝ)/8) ∧ Real.exp ((-16985/1048576 : ℝ)/8) ≤ (19959545573610563/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16985/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1465_exp_lower : (92011390699684011/100000000000000000 : ℝ) ≤ Real.exp ((-2664249748801/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664249748801/4000000000000 : ℝ)/8) ≤ (920113906996840111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664249748801/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1465_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909738103/1000000000000 : ℝ) ≤ 4*Real.exp (2123/16384 : ℝ)*Real.exp (-mu (radius 8 (16985/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909738103/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16985/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1465_exp_radius
  have hrNumeric : (491966163207/500000000000 : ℝ) ≤ Real.exp (-16985/1048576 : ℝ) ∧ Real.exp (-16985/1048576 : ℝ) ≤ (196786465283/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491966163207/500000000000 : ℝ) ≤ (radius 8 (16985/131072 : ℝ)) ∧ (radius 8 (16985/131072 : ℝ)) ≤ (196786465283/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16985/131072 : ℝ)) (491966163207/500000000000 : ℝ) (196786465283/200000000000 : ℝ) (22317725941/125000000000 : ℝ) (35708361507/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16985/131072 : ℝ)) (491966163207/500000000000 : ℝ) (196786465283/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491966163207/500000000000 : ℝ) (196786465283/200000000000 : ℝ) (991966163207/1000000000000 : ℝ) (123995770401/125000000000 : ℝ) (247983407511/250000000000 : ℝ) (495966815023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 1 (991966163207/1000000000000 : ℝ) (123995770401/125000000000 : ℝ) (247983407511/250000000000 : ℝ) (495966815023/500000000000 : ℝ) (7935599173/8000000000 : ℝ) (991949896627/1000000000000 : ℝ) (247987474123/250000000000 : ℝ) (495974948247/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 2 (7935599173/8000000000 : ℝ) (991949896627/1000000000000 : ℝ) (247987474123/250000000000 : ℝ) (495974948247/500000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 3 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 4 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 5 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 6 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16985/131072 : ℝ)) 7 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16985/131072 : ℝ))) (22317725941/125000000000 : ℝ) (35708361507/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22317725941/125000000000 : ℝ) (35708361507/200000000000 : ℝ) (147317725941/250000000000 : ℝ) (73658862971/125000000000 : ℝ) (422542077819/1000000000000 : ℝ) (105635519457/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 1 (147317725941/250000000000 : ℝ) (73658862971/125000000000 : ℝ) (422542077819/1000000000000 : ℝ) (105635519457/250000000000 : ℝ) (505906490791/1000000000000 : ℝ) (252953245399/500000000000 : ℝ) (99798146691/200000000000 : ℝ) (498990733463/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 2 (505906490791/1000000000000 : ℝ) (252953245399/500000000000 : ℝ) (99798146691/200000000000 : ℝ) (498990733463/1000000000000 : ℝ) (502448612123/1000000000000 : ℝ) (502448612131/1000000000000 : ℝ) (502436713327/1000000000000 : ℝ) (62804589167/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 3 (502448612123/1000000000000 : ℝ) (502448612131/1000000000000 : ℝ) (502436713327/1000000000000 : ℝ) (62804589167/125000000000 : ℝ) (20097706509/40000000000 : ℝ) (251221331367/500000000000 : ℝ) (502442662689/1000000000000 : ℝ) (502442662699/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 4 (20097706509/40000000000 : ℝ) (251221331367/500000000000 : ℝ) (502442662689/1000000000000 : ℝ) (502442662699/1000000000000 : ℝ) (502442662707/1000000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 5 (502442662707/1000000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 6 (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16985/131072 : ℝ))) 7 (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16985/131072 : ℝ)) hmem 8 (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16985/131072 : ℝ))) hcmem 8 (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16985/131072 : ℝ)) (495974948279/500000000000 : ℝ) (991949896561/1000000000000 : ℝ) (251221331353/500000000000 : ℝ) (502442662717/1000000000000 : ℝ) (397820036949/500000000000 : ℝ) (795640073919/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1465_exp_lower
  have heNumeric : (2054909738103/1000000000000 : ℝ)/4 ≤ Real.exp (-2664249748801/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909738103/1000000000000 : ℝ)/4 ≤ Real.exp ((2123/16384 : ℝ)-(795640073919/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2123/16384 : ℝ) (16985/131072 : ℝ) (795640073919/1000000000000 : ℝ) (2054909738103/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1466; no trusted numerical premise.
theorem cover8_leaf1466_exp_radius : (997977159712372861/1000000000000000000 : ℝ) ≤ Real.exp ((-8493/524288 : ℝ)/8) ∧ Real.exp ((-8493/524288 : ℝ)/8) ≤ (498988579856186431/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8493/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1466_exp_lower : (57507119740783597/62500000000000000 : ℝ) ≤ Real.exp ((-21313995526519/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313995526519/32000000000000 : ℝ)/8) ≤ (920113915852537553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313995526519/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1466_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727474081/250000000000 : ℝ) ≤ 4*Real.exp (16985/131072 : ℝ)*Real.exp (-mu (radius 8 (8493/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513727474081/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8493/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1466_exp_radius
  have hrNumeric : (983931388063/1000000000000 : ℝ) ≤ Real.exp (-8493/524288 : ℝ) ∧ Real.exp (-8493/524288 : ℝ) ≤ (30747855877/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983931388063/1000000000000 : ℝ) ≤ (radius 8 (8493/65536 : ℝ)) ∧ (radius 8 (8493/65536 : ℝ)) ≤ (30747855877/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8493/65536 : ℝ)) (983931388063/1000000000000 : ℝ) (30747855877/31250000000 : ℝ) (89273489321/500000000000 : ℝ) (178546978649/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8493/65536 : ℝ)) (983931388063/1000000000000 : ℝ) (30747855877/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983931388063/1000000000000 : ℝ) (30747855877/31250000000 : ℝ) (991965694031/1000000000000 : ℝ) (61997855877/62500000000 : ℝ) (991933157053/1000000000000 : ℝ) (198386631411/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 1 (991965694031/1000000000000 : ℝ) (61997855877/62500000000 : ℝ) (991933157053/1000000000000 : ℝ) (198386631411/200000000000 : ℝ) (495974712771/500000000000 : ℝ) (123993678193/125000000000 : ℝ) (3874802443/3906250000 : ℝ) (991949425411/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 2 (495974712771/500000000000 : ℝ) (123993678193/125000000000 : ℝ) (3874802443/3906250000 : ℝ) (991949425411/1000000000000 : ℝ) (39677977019/40000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 3 (39677977019/40000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 4 (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 5 (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 6 (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8493/65536 : ℝ)) 7 (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8493/65536 : ℝ))) (89273489321/500000000000 : ℝ) (178546978649/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89273489321/500000000000 : ℝ) (178546978649/1000000000000 : ℝ) (589273489321/1000000000000 : ℝ) (23570939573/40000000000 : ℝ) (422548196827/1000000000000 : ℝ) (105637049209/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 1 (589273489321/1000000000000 : ℝ) (23570939573/40000000000 : ℝ) (422548196827/1000000000000 : ℝ) (105637049209/250000000000 : ℝ) (252955421537/500000000000 : ℝ) (505910843081/1000000000000 : ℝ) (124748860303/250000000000 : ℝ) (24949772061/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 2 (252955421537/500000000000 : ℝ) (505910843081/1000000000000 : ℝ) (124748860303/250000000000 : ℝ) (24949772061/50000000000 : ℝ) (502453142143/1000000000000 : ℝ) (502453142151/1000000000000 : ℝ) (251220622339/500000000000 : ℝ) (251220622343/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 3 (502453142143/1000000000000 : ℝ) (502453142151/1000000000000 : ℝ) (251220622339/500000000000 : ℝ) (251220622343/500000000000 : ℝ) (50244719341/100000000000 : ℝ) (502447193419/1000000000000 : ℝ) (4019577547/8000000000 : ℝ) (62805899173/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 4 (50244719341/100000000000 : ℝ) (502447193419/1000000000000 : ℝ) (4019577547/8000000000 : ℝ) (62805899173/125000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 5 (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 6 (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8493/65536 : ℝ))) 7 (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8493/65536 : ℝ)) hmem 8 (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8493/65536 : ℝ))) hcmem 8 (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8493/65536 : ℝ)) (495974712737/500000000000 : ℝ) (495974712739/500000000000 : ℝ) (31402949587/62500000000 : ℝ) (251223596701/500000000000 : ℝ) (795647626297/1000000000000 : ℝ) (795647626317/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1466_exp_lower
  have heNumeric : (513727474081/250000000000 : ℝ)/4 ≤ Real.exp (-21313995526519/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727474081/250000000000 : ℝ)/4 ≤ Real.exp ((16985/131072 : ℝ)-(795647626317/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16985/131072 : ℝ) (8493/65536 : ℝ) (795647626317/1000000000000 : ℝ) (513727474081/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1467; no trusted numerical premise.
theorem cover8_leaf1467_exp_radius : (199595408148846351/200000000000000000 : ℝ) ≤ Real.exp ((-16987/1048576 : ℝ)/8) ∧ Real.exp ((-16987/1048576 : ℝ)/8) ≤ (249494260186057939/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16987/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1467_exp_lower : (115014240593029317/125000000000000000 : ℝ) ≤ Real.exp ((-10656996526307/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656996526307/16000000000000 : ℝ)/8) ≤ (920113924744234537/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656996526307/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1467_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727513797/250000000000 : ℝ) ≤ 4*Real.exp (8493/65536 : ℝ)*Real.exp (-mu (radius 8 (16987/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513727513797/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16987/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1467_exp_radius
  have hrNumeric : (491965224857/500000000000 : ℝ) ≤ Real.exp (-16987/1048576 : ℝ) ∧ Real.exp (-16987/1048576 : ℝ) ≤ (196786089943/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491965224857/500000000000 : ℝ) ≤ (radius 8 (16987/131072 : ℝ)) ∧ (radius 8 (16987/131072 : ℝ)) ≤ (196786089943/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16987/131072 : ℝ)) (491965224857/500000000000 : ℝ) (196786089943/200000000000 : ℝ) (178552149591/1000000000000 : ℝ) (178552149597/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16987/131072 : ℝ)) (491965224857/500000000000 : ℝ) (196786089943/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491965224857/500000000000 : ℝ) (196786089943/200000000000 : ℝ) (991965224857/1000000000000 : ℝ) (495982612429/500000000000 : ℝ) (991932684063/1000000000000 : ℝ) (198386536813/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 1 (991965224857/1000000000000 : ℝ) (495982612429/500000000000 : ℝ) (991932684063/1000000000000 : ℝ) (198386536813/200000000000 : ℝ) (49597447723/50000000000 : ℝ) (495974477231/500000000000 : ℝ) (495974477163/500000000000 : ℝ) (991948954329/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 2 (49597447723/50000000000 : ℝ) (495974477231/500000000000 : ℝ) (495974477163/500000000000 : ℝ) (991948954329/1000000000000 : ℝ) (991948954393/1000000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 3 (991948954393/1000000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 4 (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 5 (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 6 (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16987/131072 : ℝ)) 7 (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16987/131072 : ℝ))) (178552149591/1000000000000 : ℝ) (178552149597/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178552149591/1000000000000 : ℝ) (178552149597/1000000000000 : ℝ) (117855214959/200000000000 : ℝ) (589276074799/1000000000000 : ℝ) (422554315551/1000000000000 : ℝ) (422554315559/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 1 (117855214959/200000000000 : ℝ) (589276074799/1000000000000 : ℝ) (422554315551/1000000000000 : ℝ) (422554315559/1000000000000 : ℝ) (505915195173/1000000000000 : ℝ) (505915195179/1000000000000 : ℝ) (499000148753/1000000000000 : ℝ) (12475003719/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 2 (505915195173/1000000000000 : ℝ) (505915195179/1000000000000 : ℝ) (499000148753/1000000000000 : ℝ) (12475003719/25000000000 : ℝ) (502457671963/1000000000000 : ℝ) (50245767197/100000000000 : ℝ) (125611443957/250000000000 : ℝ) (100489155167/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 3 (502457671963/1000000000000 : ℝ) (50245767197/100000000000 : ℝ) (125611443957/250000000000 : ℝ) (100489155167/200000000000 : ℝ) (100490344779/200000000000 : ℝ) (502451723903/1000000000000 : ℝ) (25122586193/50000000000 : ℝ) (125612930967/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 4 (100490344779/200000000000 : ℝ) (502451723903/1000000000000 : ℝ) (25122586193/50000000000 : ℝ) (125612930967/250000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 5 (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 6 (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16987/131072 : ℝ))) 7 (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16987/131072 : ℝ)) hmem 8 (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16987/131072 : ℝ))) hcmem 8 (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16987/131072 : ℝ)) (123993619299/125000000000 : ℝ) (247987238599/250000000000 : ℝ) (502451723877/1000000000000 : ℝ) (251225861943/500000000000 : ℝ) (795655178383/1000000000000 : ℝ) (397827589201/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1467_exp_lower
  have heNumeric : (513727513797/250000000000 : ℝ)/4 ≤ Real.exp (-10656996526307/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727513797/250000000000 : ℝ)/4 ≤ Real.exp ((8493/65536 : ℝ)-(397827589201/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8493/65536 : ℝ) (16987/131072 : ℝ) (397827589201/500000000000 : ℝ) (513727513797/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1468; no trusted numerical premise.
theorem cover8_leaf1468_exp_radius : (997976921776104831/1000000000000000000 : ℝ) ≤ Real.exp ((-4247/262144 : ℝ)/8) ∧ Real.exp ((-4247/262144 : ℝ)/8) ≤ (7796694701375819/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-4247/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1468_exp_lower : (184022786733903153/200000000000000000 : ℝ) ≤ Real.exp ((-4262798113873/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262798113873/6400000000000 : ℝ)/8) ≤ (460056966834757883/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262798113873/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1468_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727553663/250000000000 : ℝ) ≤ 4*Real.exp (16987/131072 : ℝ)*Real.exp (-mu (radius 8 (4247/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513727553663/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4247/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1468_exp_radius
  have hrNumeric : (196785902273/200000000000 : ℝ) ≤ Real.exp (-4247/262144 : ℝ) ∧ Real.exp (-4247/262144 : ℝ) ≤ (491964755683/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196785902273/200000000000 : ℝ) ≤ (radius 8 (4247/32768 : ℝ)) ∧ (radius 8 (4247/32768 : ℝ)) ≤ (491964755683/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4247/32768 : ℝ)) (196785902273/200000000000 : ℝ) (491964755683/500000000000 : ℝ) (2789958131/15625000000 : ℝ) (178557320391/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4247/32768 : ℝ)) (196785902273/200000000000 : ℝ) (491964755683/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196785902273/200000000000 : ℝ) (491964755683/500000000000 : ℝ) (495982377841/500000000000 : ℝ) (991964755683/1000000000000 : ℝ) (991932211073/1000000000000 : ℝ) (495966105537/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 1 (495982377841/500000000000 : ℝ) (991964755683/1000000000000 : ℝ) (991932211073/1000000000000 : ℝ) (495966105537/500000000000 : ℝ) (991948483377/1000000000000 : ℝ) (991948483379/1000000000000 : ℝ) (247987120811/250000000000 : ℝ) (495974241623/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 2 (991948483377/1000000000000 : ℝ) (991948483379/1000000000000 : ℝ) (247987120811/250000000000 : ℝ) (495974241623/500000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 3 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 4 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 5 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 6 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4247/32768 : ℝ)) 7 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4247/32768 : ℝ))) (2789958131/15625000000 : ℝ) (178557320391/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2789958131/15625000000 : ℝ) (178557320391/1000000000000 : ℝ) (18414958131/31250000000 : ℝ) (147319665049/250000000000 : ℝ) (211280217001/500000000000 : ℝ) (422560434011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 1 (18414958131/31250000000 : ℝ) (147319665049/250000000000 : ℝ) (211280217001/500000000000 : ℝ) (422560434011/1000000000000 : ℝ) (505919547097/1000000000000 : ℝ) (15809985847/31250000000 : ℝ) (499004856087/1000000000000 : ℝ) (99800971219/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 2 (505919547097/1000000000000 : ℝ) (15809985847/31250000000 : ℝ) (499004856087/1000000000000 : ℝ) (99800971219/200000000000 : ℝ) (62807775199/125000000000 : ℝ) (78509719/156250000 : ℝ) (502450306787/1000000000000 : ℝ) (100490061359/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 3 (62807775199/125000000000 : ℝ) (78509719/156250000 : ℝ) (502450306787/1000000000000 : ℝ) (100490061359/200000000000 : ℝ) (502456254189/1000000000000 : ℝ) (251228127099/500000000000 : ℝ) (251228127077/500000000000 : ℝ) (502456254163/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 4 (502456254189/1000000000000 : ℝ) (251228127099/500000000000 : ℝ) (251228127077/500000000000 : ℝ) (502456254163/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 5 (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 6 (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4247/32768 : ℝ))) 7 (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4247/32768 : ℝ)) hmem 8 (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4247/32768 : ℝ))) hcmem 8 (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4247/32768 : ℝ)) (99194848331/100000000000 : ℝ) (991948483313/1000000000000 : ℝ) (502456254171/1000000000000 : ℝ) (502456254181/1000000000000 : ℝ) (12432230159/15625000000 : ℝ) (159132546039/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1468_exp_lower
  have heNumeric : (513727553663/250000000000 : ℝ)/4 ≤ Real.exp (-4262798113873/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727553663/250000000000 : ℝ)/4 ≤ Real.exp ((16987/131072 : ℝ)-(159132546039/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16987/131072 : ℝ) (4247/32768 : ℝ) (159132546039/200000000000 : ℝ) (513727553663/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1469; no trusted numerical premise.
theorem cover8_leaf1469_exp_radius : (997976802807992089/1000000000000000000 : ℝ) ≤ Real.exp ((-16989/1048576 : ℝ)/8) ∧ Real.exp ((-16989/1048576 : ℝ)/8) ≤ (99797680280799209/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16989/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1469_exp_lower : (230028485657411599/250000000000000000 : ℝ) ≤ Real.exp ((-1065699403821/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065699403821/1600000000000 : ℝ)/8) ≤ (920113942629646397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065699403821/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1469_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910374739/1000000000000 : ℝ) ≤ 4*Real.exp (4247/32768 : ℝ)*Real.exp (-mu (radius 8 (16989/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910374739/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16989/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1469_exp_radius
  have hrNumeric : (983928573017/1000000000000 : ℝ) ≤ Real.exp (-16989/1048576 : ℝ) ∧ Real.exp (-16989/1048576 : ℝ) ≤ (491964286509/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983928573017/1000000000000 : ℝ) ≤ (radius 8 (16989/131072 : ℝ)) ∧ (radius 8 (16989/131072 : ℝ)) ≤ (491964286509/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16989/131072 : ℝ)) (983928573017/1000000000000 : ℝ) (491964286509/500000000000 : ℝ) (89281245509/500000000000 : ℝ) (7142499641/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16989/131072 : ℝ)) (983928573017/1000000000000 : ℝ) (491964286509/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983928573017/1000000000000 : ℝ) (491964286509/500000000000 : ℝ) (247991071627/250000000000 : ℝ) (991964286509/1000000000000 : ℝ) (991931738083/1000000000000 : ℝ) (247982934521/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 1 (247991071627/250000000000 : ℝ) (991964286509/1000000000000 : ℝ) (991931738083/1000000000000 : ℝ) (247982934521/250000000000 : ℝ) (198389602459/200000000000 : ℝ) (991948012297/1000000000000 : ℝ) (495974006081/500000000000 : ℝ) (247987003041/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 2 (198389602459/200000000000 : ℝ) (991948012297/1000000000000 : ℝ) (495974006081/500000000000 : ℝ) (247987003041/250000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 3 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 4 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 5 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 6 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16989/131072 : ℝ)) 7 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16989/131072 : ℝ))) (89281245509/500000000000 : ℝ) (7142499641/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89281245509/500000000000 : ℝ) (7142499641/40000000000 : ℝ) (589281245509/1000000000000 : ℝ) (589281245513/1000000000000 : ℝ) (26410409511/62500000000 : ℝ) (84513310437/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 1 (589281245509/1000000000000 : ℝ) (589281245513/1000000000000 : ℝ) (26410409511/62500000000 : ℝ) (84513310437/200000000000 : ℝ) (252961949421/500000000000 : ℝ) (505923898849/1000000000000 : ℝ) (499009563211/1000000000000 : ℝ) (499009563219/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 2 (252961949421/500000000000 : ℝ) (505923898849/1000000000000 : ℝ) (499009563211/1000000000000 : ℝ) (499009563219/1000000000000 : ℝ) (251233365513/500000000000 : ℝ) (251233365517/500000000000 : ℝ) (502454837551/1000000000000 : ℝ) (12561370939/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 3 (251233365513/500000000000 : ℝ) (251233365517/500000000000 : ℝ) (502454837551/1000000000000 : ℝ) (12561370939/25000000000 : ℝ) (15701899509/31250000000 : ℝ) (502460784297/1000000000000 : ℝ) (502460784253/1000000000000 : ℝ) (251230392131/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 4 (15701899509/31250000000 : ℝ) (502460784297/1000000000000 : ℝ) (502460784253/1000000000000 : ℝ) (251230392131/500000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 5 (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 6 (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16989/131072 : ℝ))) 7 (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16989/131072 : ℝ)) hmem 8 (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16989/131072 : ℝ))) hcmem 8 (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16989/131072 : ℝ)) (247987003057/250000000000 : ℝ) (991948012231/1000000000000 : ℝ) (50246078427/100000000000 : ℝ) (12561519607/25000000000 : ℝ) (159134056333/200000000000 : ℝ) (159134056337/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1469_exp_lower
  have heNumeric : (2054910374739/1000000000000 : ℝ)/4 ≤ Real.exp (-1065699403821/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910374739/1000000000000 : ℝ)/4 ≤ Real.exp ((4247/32768 : ℝ)-(159134056337/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4247/32768 : ℝ) (16989/131072 : ℝ) (159134056337/200000000000 : ℝ) (2054910374739/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1470; no trusted numerical premise.
theorem cover8_leaf1470_exp_radius : (997976683839893529/1000000000000000000 : ℝ) ≤ Real.exp ((-8495/524288 : ℝ)/8) ∧ Real.exp ((-8495/524288 : ℝ)/8) ≤ (99797668383989353/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8495/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1470_exp_lower : (460056975812198201/500000000000000000 : ℝ) ≤ Real.exp ((-21313985573843/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313985573843/32000000000000 : ℝ)/8) ≤ (920113951624396403/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313985573843/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1470_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982107089/200000000000 : ℝ) ≤ 4*Real.exp (16989/131072 : ℝ)*Real.exp (-mu (radius 8 (8495/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410982107089/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8495/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1470_exp_radius
  have hrNumeric : (98392763467/100000000000 : ℝ) ≤ Real.exp (-8495/524288 : ℝ) ∧ Real.exp (-8495/524288 : ℝ) ≤ (983927634671/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98392763467/100000000000 : ℝ) ≤ (radius 8 (8495/65536 : ℝ)) ∧ (radius 8 (8495/65536 : ℝ)) ≤ (983927634671/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8495/65536 : ℝ)) (98392763467/100000000000 : ℝ) (983927634671/1000000000000 : ℝ) (44641915373/250000000000 : ℝ) (89283830749/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8495/65536 : ℝ)) (98392763467/100000000000 : ℝ) (983927634671/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98392763467/100000000000 : ℝ) (983927634671/1000000000000 : ℝ) (198392763467/200000000000 : ℝ) (123995477167/125000000000 : ℝ) (991931265093/1000000000000 : ℝ) (198386253019/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 1 (198392763467/200000000000 : ℝ) (123995477167/125000000000 : ℝ) (991931265093/1000000000000 : ℝ) (198386253019/200000000000 : ℝ) (495973770607/500000000000 : ℝ) (30998360663/31250000000 : ℝ) (24798688527/25000000000 : ℝ) (495973770541/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 2 (495973770607/500000000000 : ℝ) (30998360663/31250000000 : ℝ) (24798688527/25000000000 : ℝ) (495973770541/500000000000 : ℝ) (991947541147/1000000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 3 (991947541147/1000000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 4 (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 5 (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 6 (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8495/65536 : ℝ)) 7 (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8495/65536 : ℝ))) (44641915373/250000000000 : ℝ) (89283830749/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44641915373/250000000000 : ℝ) (89283830749/500000000000 : ℝ) (294641915373/500000000000 : ℝ) (589283830749/1000000000000 : ℝ) (52821583759/125000000000 : ℝ) (660269797/1562500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 1 (294641915373/500000000000 : ℝ) (589283830749/1000000000000 : ℝ) (52821583759/125000000000 : ℝ) (660269797/1562500000 : ℝ) (505928250409/1000000000000 : ℝ) (101185650083/200000000000 : ℝ) (3992114161/8000000000 : ℝ) (124753567533/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 2 (505928250409/1000000000000 : ℝ) (101185650083/200000000000 : ℝ) (3992114161/8000000000 : ℝ) (124753567533/250000000000 : ℝ) (502471260267/1000000000000 : ℝ) (251235630137/500000000000 : ℝ) (502459368121/1000000000000 : ℝ) (502459368129/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 3 (502471260267/1000000000000 : ℝ) (251235630137/500000000000 : ℝ) (502459368121/1000000000000 : ℝ) (502459368129/1000000000000 : ℝ) (251232657097/500000000000 : ℝ) (251232657101/500000000000 : ℝ) (251232657079/500000000000 : ℝ) (502465314167/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 4 (251232657097/500000000000 : ℝ) (251232657101/500000000000 : ℝ) (251232657079/500000000000 : ℝ) (502465314167/1000000000000 : ℝ) (3925510267/7812500000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 5 (3925510267/7812500000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 6 (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8495/65536 : ℝ))) 7 (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8495/65536 : ℝ)) hmem 8 (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8495/65536 : ℝ))) hcmem 8 (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8495/65536 : ℝ)) (495973770573/500000000000 : ℝ) (991947541149/1000000000000 : ℝ) (20098612567/40000000000 : ℝ) (100493062837/200000000000 : ℝ) (159135566571/200000000000 : ℝ) (397838916437/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1470_exp_lower
  have heNumeric : (410982107089/200000000000 : ℝ)/4 ≤ Real.exp (-21313985573843/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982107089/200000000000 : ℝ)/4 ≤ Real.exp ((16989/131072 : ℝ)-(397838916437/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16989/131072 : ℝ) (8495/65536 : ℝ) (397838916437/500000000000 : ℝ) (410982107089/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1471; no trusted numerical premise.
theorem cover8_leaf1471_exp_radius : (997976564871809151/1000000000000000000 : ℝ) ≤ Real.exp ((-16991/1048576 : ℝ)/8) ∧ Real.exp ((-16991/1048576 : ℝ)/8) ≤ (7796691913061009/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-16991/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1471_exp_lower : (920113960653880797/1000000000000000000 : ℝ) ≤ Real.exp ((-10656991530801/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656991530801/16000000000000 : ℝ)/8) ≤ (460056980326940399/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656991530801/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1471_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910696771/1000000000000 : ℝ) ≤ 4*Real.exp (8495/65536 : ℝ)*Real.exp (-mu (radius 8 (16991/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910696771/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16991/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1471_exp_radius
  have hrNumeric : (245981674081/250000000000 : ℝ) ≤ Real.exp (-16991/1048576 : ℝ) ∧ Real.exp (-16991/1048576 : ℝ) ≤ (39357067853/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245981674081/250000000000 : ℝ) ≤ (radius 8 (16991/131072 : ℝ)) ∧ (radius 8 (16991/131072 : ℝ)) ≤ (39357067853/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16991/131072 : ℝ)) (245981674081/250000000000 : ℝ) (39357067853/40000000000 : ℝ) (35714566361/200000000000 : ℝ) (178572831811/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16991/131072 : ℝ)) (245981674081/250000000000 : ℝ) (39357067853/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245981674081/250000000000 : ℝ) (39357067853/40000000000 : ℝ) (495981674081/500000000000 : ℝ) (991963348163/1000000000000 : ℝ) (991930792103/1000000000000 : ℝ) (198386158421/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 1 (495981674081/500000000000 : ℝ) (991963348163/1000000000000 : ℝ) (991930792103/1000000000000 : ℝ) (198386158421/200000000000 : ℝ) (247986767533/250000000000 : ℝ) (495973535067/500000000000 : ℝ) (495973534999/500000000000 : ℝ) (991947070001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 2 (247986767533/250000000000 : ℝ) (495973535067/500000000000 : ℝ) (495973534999/500000000000 : ℝ) (991947070001/1000000000000 : ℝ) (198389414013/200000000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 3 (198389414013/200000000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 4 (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 5 (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 6 (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16991/131072 : ℝ)) 7 (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16991/131072 : ℝ))) (35714566361/200000000000 : ℝ) (178572831811/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35714566361/200000000000 : ℝ) (178572831811/1000000000000 : ℝ) (294643207951/500000000000 : ℝ) (294643207953/500000000000 : ℝ) (422578787689/1000000000000 : ℝ) (422578787697/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 1 (294643207951/500000000000 : ℝ) (294643207953/500000000000 : ℝ) (422578787689/1000000000000 : ℝ) (422578787697/1000000000000 : ℝ) (101186520359/200000000000 : ℝ) (252966300901/500000000000 : ℝ) (249509488413/500000000000 : ℝ) (249509488417/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 2 (101186520359/200000000000 : ℝ) (252966300901/500000000000 : ℝ) (249509488413/500000000000 : ℝ) (249509488417/500000000000 : ℝ) (50247578931/100000000000 : ℝ) (251237894659/500000000000 : ℝ) (251231949247/500000000000 : ℝ) (502463898503/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 3 (50247578931/100000000000 : ℝ) (251237894659/500000000000 : ℝ) (251231949247/500000000000 : ℝ) (502463898503/1000000000000 : ℝ) (251234921951/500000000000 : ℝ) (502469843911/1000000000000 : ℝ) (251234921933/500000000000 : ℝ) (125617460969/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 4 (251234921951/500000000000 : ℝ) (502469843911/1000000000000 : ℝ) (251234921933/500000000000 : ℝ) (125617460969/250000000000 : ℝ) (125617460971/250000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 5 (125617460971/250000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 6 (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16991/131072 : ℝ))) 7 (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16991/131072 : ℝ)) hmem 8 (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16991/131072 : ℝ))) hcmem 8 (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16991/131072 : ℝ)) (61996691879/62500000000 : ℝ) (247986767517/250000000000 : ℝ) (502469843883/1000000000000 : ℝ) (251234921947/500000000000 : ℝ) (795685383739/1000000000000 : ℝ) (795685383761/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1471_exp_lower
  have heNumeric : (2054910696771/1000000000000 : ℝ)/4 ≤ Real.exp (-10656991530801/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910696771/1000000000000 : ℝ)/4 ≤ Real.exp ((8495/65536 : ℝ)-(795685383761/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8495/65536 : ℝ) (16991/131072 : ℝ) (795685383761/1000000000000 : ℝ) (2054910696771/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1472; no trusted numerical premise.
theorem cover8_leaf1472_exp_radius : (249494111475934739/250000000000000000 : ℝ) ≤ Real.exp ((-531/32768 : ℝ)/8) ∧ Real.exp ((-531/32768 : ℝ)/8) ≤ (997976445903738957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-531/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1472_exp_lower : (920113969718444627/1000000000000000000 : ℝ) ≤ Real.exp ((-21313980539601/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313980539601/32000000000000 : ℝ)/8) ≤ (230028492429611157/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313980539601/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1472_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910858723/1000000000000 : ℝ) ≤ 4*Real.exp (16991/131072 : ℝ)*Real.exp (-mu (radius 8 (531/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910858723/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (531/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1472_exp_radius
  have hrNumeric : (983925757979/1000000000000 : ℝ) ≤ Real.exp (-531/32768 : ℝ) ∧ Real.exp (-531/32768 : ℝ) ≤ (49196287899/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983925757979/1000000000000 : ℝ) ≤ (radius 8 (531/4096 : ℝ)) ∧ (radius 8 (531/4096 : ℝ)) ≤ (49196287899/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (531/4096 : ℝ)) (983925757979/1000000000000 : ℝ) (49196287899/50000000000 : ℝ) (89289000979/500000000000 : ℝ) (44644500491/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (531/4096 : ℝ)) (983925757979/1000000000000 : ℝ) (49196287899/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (531/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983925757979/1000000000000 : ℝ) (49196287899/50000000000 : ℝ) (991962878989/1000000000000 : ℝ) (99196287899/100000000000 : ℝ) (495965159557/500000000000 : ℝ) (247982579779/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (531/4096 : ℝ)) 1 (991962878989/1000000000000 : ℝ) (99196287899/100000000000 : ℝ) (495965159557/500000000000 : ℝ) (247982579779/250000000000 : ℝ) (991946599051/1000000000000 : ℝ) (991946599053/1000000000000 : ℝ) (991946598917/1000000000000 : ℝ) (24798664973/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (531/4096 : ℝ)) 2 (991946599051/1000000000000 : ℝ) (991946599053/1000000000000 : ℝ) (991946598917/1000000000000 : ℝ) (24798664973/25000000000 : ℝ) (123993324873/125000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (531/4096 : ℝ)) 3 (123993324873/125000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (531/4096 : ℝ)) 4 (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (531/4096 : ℝ)) 5 (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (531/4096 : ℝ)) 6 (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (531/4096 : ℝ)) 7 (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (531/4096 : ℝ))) (89289000979/500000000000 : ℝ) (44644500491/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89289000979/500000000000 : ℝ) (44644500491/250000000000 : ℝ) (589289000979/1000000000000 : ℝ) (294644500491/500000000000 : ℝ) (105646226257/250000000000 : ℝ) (105646226259/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 1 (589289000979/1000000000000 : ℝ) (294644500491/500000000000 : ℝ) (105646226257/250000000000 : ℝ) (105646226259/250000000000 : ℝ) (505936953003/1000000000000 : ℝ) (505936953009/1000000000000 : ℝ) (249511841659/500000000000 : ℝ) (19960947333/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 2 (505936953003/1000000000000 : ℝ) (505936953009/1000000000000 : ℝ) (249511841659/500000000000 : ℝ) (19960947333/40000000000 : ℝ) (6281003977/12500000000 : ℝ) (502480318167/1000000000000 : ℝ) (251234214337/500000000000 : ℝ) (502468428681/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 3 (6281003977/12500000000 : ℝ) (502480318167/1000000000000 : ℝ) (251234214337/500000000000 : ℝ) (502468428681/1000000000000 : ℝ) (502474373417/1000000000000 : ℝ) (31404648339/62500000000 : ℝ) (502474373381/1000000000000 : ℝ) (502474373389/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 4 (502474373417/1000000000000 : ℝ) (31404648339/62500000000 : ℝ) (502474373381/1000000000000 : ℝ) (502474373389/1000000000000 : ℝ) (502474373399/1000000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 5 (502474373399/1000000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 6 (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (531/4096 : ℝ))) 7 (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (531/4096 : ℝ)) hmem 8 (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (531/4096 : ℝ))) hcmem 8 (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (531/4096 : ℝ)) (991946598983/1000000000000 : ℝ) (991946598987/1000000000000 : ℝ) (251237186699/500000000000 : ℝ) (502474373407/1000000000000 : ℝ) (31827717373/40000000000 : ℝ) (795692934343/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1472_exp_lower
  have heNumeric : (2054910858723/1000000000000 : ℝ)/4 ≤ Real.exp (-21313980539601/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910858723/1000000000000 : ℝ)/4 ≤ Real.exp ((16991/131072 : ℝ)-(795692934343/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16991/131072 : ℝ) (531/4096 : ℝ) (795692934343/1000000000000 : ℝ) (2054910858723/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1473; no trusted numerical premise.
theorem cover8_leaf1473_exp_radius : (498988163467841471/500000000000000000 : ℝ) ≤ Real.exp ((-16993/1048576 : ℝ)/8) ∧ Real.exp ((-16993/1048576 : ℝ)/8) ≤ (997976326935682943/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16993/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1473_exp_lower : (920113978816247663/1000000000000000000 : ℝ) ≤ Real.exp ((-666061812761/1000000000000 : ℝ)/8) ∧ Real.exp ((-666061812761/1000000000000 : ℝ)/8) ≤ (57507123676015479/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666061812761/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1473_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491102127/100000000000 : ℝ) ≤ 4*Real.exp (531/4096 : ℝ)*Real.exp (-mu (radius 8 (16993/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205491102127/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16993/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1473_exp_radius
  have hrNumeric : (491962409817/500000000000 : ℝ) ≤ Real.exp (-16993/1048576 : ℝ) ∧ Real.exp (-16993/1048576 : ℝ) ≤ (196784963927/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491962409817/500000000000 : ℝ) ≤ (radius 8 (16993/131072 : ℝ)) ∧ (radius 8 (16993/131072 : ℝ)) ≤ (196784963927/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16993/131072 : ℝ)) (491962409817/500000000000 : ℝ) (196784963927/200000000000 : ℝ) (178583171957/1000000000000 : ℝ) (178583171963/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16993/131072 : ℝ)) (491962409817/500000000000 : ℝ) (196784963927/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491962409817/500000000000 : ℝ) (196784963927/200000000000 : ℝ) (991962409817/1000000000000 : ℝ) (495981204909/500000000000 : ℝ) (7935438769/8000000000 : ℝ) (495964923063/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 1 (991962409817/1000000000000 : ℝ) (495981204909/500000000000 : ℝ) (7935438769/8000000000 : ℝ) (495964923063/500000000000 : ℝ) (991946127971/1000000000000 : ℝ) (247986531993/250000000000 : ℝ) (991946127837/1000000000000 : ℝ) (991946127839/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 2 (991946127971/1000000000000 : ℝ) (247986531993/250000000000 : ℝ) (991946127837/1000000000000 : ℝ) (991946127839/1000000000000 : ℝ) (30998316497/31250000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 3 (30998316497/31250000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 4 (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 5 (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 6 (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16993/131072 : ℝ)) 7 (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16993/131072 : ℝ))) (178583171957/1000000000000 : ℝ) (178583171963/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178583171957/1000000000000 : ℝ) (178583171963/1000000000000 : ℝ) (294645792989/500000000000 : ℝ) (294645792991/500000000000 : ℝ) (422591022097/1000000000000 : ℝ) (84518204421/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 1 (294645792989/500000000000 : ℝ) (294645792991/500000000000 : ℝ) (422591022097/1000000000000 : ℝ) (84518204421/200000000000 : ℝ) (505941304037/1000000000000 : ℝ) (126485326011/250000000000 : ℝ) (124757097401/250000000000 : ℝ) (124757097403/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 2 (505941304037/1000000000000 : ℝ) (126485326011/250000000000 : ℝ) (124757097401/250000000000 : ℝ) (124757097403/250000000000 : ℝ) (25124242341/50000000000 : ℝ) (125621211707/250000000000 : ℝ) (502472958663/1000000000000 : ℝ) (502472958671/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 3 (25124242341/50000000000 : ℝ) (125621211707/250000000000 : ℝ) (502472958663/1000000000000 : ℝ) (502472958671/1000000000000 : ℝ) (502478902741/1000000000000 : ℝ) (2009915611/4000000000 : ℝ) (251239451353/500000000000 : ℝ) (100495780543/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 4 (502478902741/1000000000000 : ℝ) (2009915611/4000000000 : ℝ) (251239451353/500000000000 : ℝ) (100495780543/200000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 5 (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 6 (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16993/131072 : ℝ))) 7 (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16993/131072 : ℝ)) hmem 8 (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16993/131072 : ℝ))) hcmem 8 (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16993/131072 : ℝ)) (991946127903/1000000000000 : ℝ) (495973063953/500000000000 : ℝ) (502478902723/1000000000000 : ℝ) (502478902733/1000000000000 : ℝ) (795700484617/1000000000000 : ℝ) (198925121159/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1473_exp_lower
  have heNumeric : (205491102127/100000000000 : ℝ)/4 ≤ Real.exp (-666061812761/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491102127/100000000000 : ℝ)/4 ≤ Real.exp ((531/4096 : ℝ)-(198925121159/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (531/4096 : ℝ) (16993/131072 : ℝ) (198925121159/250000000000 : ℝ) (205491102127/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1474; no trusted numerical premise.
theorem cover8_leaf1474_exp_radius : (997976207967641111/1000000000000000000 : ℝ) ≤ Real.exp ((-8497/524288 : ℝ)/8) ∧ Real.exp ((-8497/524288 : ℝ)/8) ≤ (124747025995955139/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8497/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1474_exp_lower : (920113987950165263/1000000000000000000 : ℝ) ≤ Real.exp ((-4262795093411/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262795093411/6400000000000 : ℝ)/8) ≤ (57507124246885329/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262795093411/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1474_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455592231/500000000000 : ℝ) ≤ 4*Real.exp (16993/131072 : ℝ)*Real.exp (-mu (radius 8 (8497/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455592231/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8497/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1474_exp_radius
  have hrNumeric : (983923881291/1000000000000 : ℝ) ≤ Real.exp (-8497/524288 : ℝ) ∧ Real.exp (-8497/524288 : ℝ) ≤ (245980970323/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983923881291/1000000000000 : ℝ) ≤ (radius 8 (8497/65536 : ℝ)) ∧ (radius 8 (8497/65536 : ℝ)) ≤ (245980970323/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8497/65536 : ℝ)) (983923881291/1000000000000 : ℝ) (245980970323/250000000000 : ℝ) (178588341789/1000000000000 : ℝ) (44647085449/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8497/65536 : ℝ)) (983923881291/1000000000000 : ℝ) (245980970323/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983923881291/1000000000000 : ℝ) (245980970323/250000000000 : ℝ) (198392388129/200000000000 : ℝ) (495980970323/500000000000 : ℝ) (61995585821/62500000000 : ℝ) (495964686569/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 1 (198392388129/200000000000 : ℝ) (495980970323/500000000000 : ℝ) (61995585821/62500000000 : ℝ) (495964686569/500000000000 : ℝ) (99194565689/100000000000 : ℝ) (247986414223/250000000000 : ℝ) (247986414189/250000000000 : ℝ) (991945656759/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 2 (99194565689/100000000000 : ℝ) (247986414223/250000000000 : ℝ) (247986414189/250000000000 : ℝ) (991945656759/1000000000000 : ℝ) (991945656823/1000000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 3 (991945656823/1000000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 4 (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 5 (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 6 (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8497/65536 : ℝ)) 7 (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8497/65536 : ℝ))) (178588341789/1000000000000 : ℝ) (44647085449/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178588341789/1000000000000 : ℝ) (44647085449/250000000000 : ℝ) (294647085447/500000000000 : ℝ) (294647085449/500000000000 : ℝ) (422597138879/1000000000000 : ℝ) (52824642361/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 1 (294647085447/500000000000 : ℝ) (294647085449/500000000000 : ℝ) (422597138879/1000000000000 : ℝ) (52824642361/125000000000 : ℝ) (252972827443/500000000000 : ℝ) (505945654893/1000000000000 : ℝ) (499033095673/1000000000000 : ℝ) (499033095681/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 2 (252972827443/500000000000 : ℝ) (505945654893/1000000000000 : ℝ) (499033095673/1000000000000 : ℝ) (499033095681/1000000000000 : ℝ) (502489375279/1000000000000 : ℝ) (502489375287/1000000000000 : ℝ) (502477488451/1000000000000 : ℝ) (502477488459/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 3 (502489375279/1000000000000 : ℝ) (502489375287/1000000000000 : ℝ) (502477488451/1000000000000 : ℝ) (502477488459/1000000000000 : ℝ) (100496686373/200000000000 : ℝ) (502483431873/1000000000000 : ℝ) (502483431829/1000000000000 : ℝ) (251241715919/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 4 (100496686373/200000000000 : ℝ) (502483431873/1000000000000 : ℝ) (502483431829/1000000000000 : ℝ) (251241715919/500000000000 : ℝ) (502483431847/1000000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 5 (502483431847/1000000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 6 (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8497/65536 : ℝ))) 7 (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8497/65536 : ℝ)) hmem 8 (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8497/65536 : ℝ))) hcmem 8 (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8497/65536 : ℝ)) (495972828411/500000000000 : ℝ) (495972828413/500000000000 : ℝ) (251241715923/500000000000 : ℝ) (31405214491/62500000000 : ℝ) (159141606919/200000000000 : ℝ) (159141606923/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1474_exp_lower
  have heNumeric : (1027455592231/500000000000 : ℝ)/4 ≤ Real.exp (-4262795093411/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455592231/500000000000 : ℝ)/4 ≤ Real.exp ((16993/131072 : ℝ)-(159141606923/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16993/131072 : ℝ) (8497/65536 : ℝ) (159141606923/200000000000 : ℝ) (1027455592231/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1450_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1450_certificate
#check SmaleRate.Proofs.cover8_leaf1451_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1451_certificate
#check SmaleRate.Proofs.cover8_leaf1452_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1452_certificate
#check SmaleRate.Proofs.cover8_leaf1453_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1453_certificate
#check SmaleRate.Proofs.cover8_leaf1454_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1454_certificate
#check SmaleRate.Proofs.cover8_leaf1455_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1455_certificate
#check SmaleRate.Proofs.cover8_leaf1456_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1456_certificate
#check SmaleRate.Proofs.cover8_leaf1457_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1457_certificate
#check SmaleRate.Proofs.cover8_leaf1458_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1458_certificate
#check SmaleRate.Proofs.cover8_leaf1459_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1459_certificate
#check SmaleRate.Proofs.cover8_leaf1460_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1460_certificate
#check SmaleRate.Proofs.cover8_leaf1461_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1461_certificate
#check SmaleRate.Proofs.cover8_leaf1462_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1462_certificate
#check SmaleRate.Proofs.cover8_leaf1463_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1463_certificate
#check SmaleRate.Proofs.cover8_leaf1464_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1464_certificate
#check SmaleRate.Proofs.cover8_leaf1465_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1465_certificate
#check SmaleRate.Proofs.cover8_leaf1466_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1466_certificate
#check SmaleRate.Proofs.cover8_leaf1467_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1467_certificate
#check SmaleRate.Proofs.cover8_leaf1468_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1468_certificate
#check SmaleRate.Proofs.cover8_leaf1469_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1469_certificate
#check SmaleRate.Proofs.cover8_leaf1470_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1470_certificate
#check SmaleRate.Proofs.cover8_leaf1471_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1471_certificate
#check SmaleRate.Proofs.cover8_leaf1472_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1472_certificate
#check SmaleRate.Proofs.cover8_leaf1473_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1473_certificate
#check SmaleRate.Proofs.cover8_leaf1474_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1474_certificate
