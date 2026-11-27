/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1625; no trusted numerical premise.
theorem cover8_leaf1625_exp_radius : (498963478208307879/500000000000000000 : ℝ) ≤ Real.exp ((-17/1024 : ℝ)/8) ∧ Real.exp ((-17/1024 : ℝ)/8) ≤ (997926956416615759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1625_exp_lower : (920114559196926399/1000000000000000000 : ℝ) ≤ Real.exp ((-2664227066397/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664227066397/4000000000000 : ℝ)/8) ≤ (575071599498079/625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664227066397/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1625_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054921390709/1000000000000 : ℝ) ≤ 4*Real.exp (2175/16384 : ℝ)*Real.exp (-mu (radius 8 (17/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2054921390709/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1625_exp_radius
  have hrNumeric : (196707096799/200000000000 : ℝ) ≤ Real.exp (-17/1024 : ℝ) ∧ Real.exp (-17/1024 : ℝ) ≤ (245883870999/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196707096799/200000000000 : ℝ) ≤ (radius 8 (17/128 : ℝ)) ∧ (radius 8 (17/128 : ℝ)) ≤ (245883870999/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17/128 : ℝ)) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17/128 : ℝ)) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) (991767741997/1000000000000 : ℝ) (495883870999/500000000000 : ℝ) (991733575107/1000000000000 : ℝ) (247933393777/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17/128 : ℝ)) 1 (991767741997/1000000000000 : ℝ) (495883870999/500000000000 : ℝ) (991733575107/1000000000000 : ℝ) (247933393777/250000000000 : ℝ) (123968832319/125000000000 : ℝ) (991750658553/1000000000000 : ℝ) (247937664601/250000000000 : ℝ) (495875329203/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17/128 : ℝ)) 2 (123968832319/125000000000 : ℝ) (991750658553/1000000000000 : ℝ) (247937664601/250000000000 : ℝ) (495875329203/500000000000 : ℝ) (495875329239/500000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17/128 : ℝ)) 3 (495875329239/500000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17/128 : ℝ)) 4 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17/128 : ℝ)) 5 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17/128 : ℝ)) 6 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17/128 : ℝ)) 7 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17/128 : ℝ))) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ) (590357556021/1000000000000 : ℝ) (23614302241/40000000000 : ℝ) (425106000949/1000000000000 : ℝ) (425106000957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 1 (590357556021/1000000000000 : ℝ) (23614302241/40000000000 : ℝ) (425106000949/1000000000000 : ℝ) (425106000957/1000000000000 : ℝ) (101546355697/200000000000 : ℝ) (507731778491/1000000000000 : ℝ) (500963611223/1000000000000 : ℝ) (50096361123/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 2 (101546355697/200000000000 : ℝ) (507731778491/1000000000000 : ℝ) (500963611223/1000000000000 : ℝ) (50096361123/100000000000 : ℝ) (252173847427/500000000000 : ℝ) (504347694861/1000000000000 : ℝ) (20173453657/40000000000 : ℝ) (504336341433/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 3 (252173847427/500000000000 : ℝ) (504347694861/1000000000000 : ℝ) (20173453657/40000000000 : ℝ) (504336341433/1000000000000 : ℝ) (504342018139/1000000000000 : ℝ) (504342018147/1000000000000 : ℝ) (504342018107/1000000000000 : ℝ) (126085504529/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 4 (504342018139/1000000000000 : ℝ) (504342018147/1000000000000 : ℝ) (504342018107/1000000000000 : ℝ) (126085504529/250000000000 : ℝ) (504342018123/1000000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 5 (504342018123/1000000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 6 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17/128 : ℝ))) 7 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17/128 : ℝ)) hmem 8 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17/128 : ℝ))) hcmem 8 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17/128 : ℝ)) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (1560172327/1953125000 : ℝ) (798808231443/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1625_exp_lower
  have heNumeric : (2054921390709/1000000000000 : ℝ)/4 ≤ Real.exp (-2664227066397/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054921390709/1000000000000 : ℝ)/4 ≤ Real.exp ((2175/16384 : ℝ)-(798808231443/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2175/16384 : ℝ) (17/128 : ℝ) (798808231443/1000000000000 : ℝ) (2054921390709/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1626; no trusted numerical premise.
theorem cover8_leaf1626_exp_radius : (498963002359880789/500000000000000000 : ℝ) ≤ Real.exp ((-2177/131072 : ℝ)/8) ∧ Real.exp ((-2177/131072 : ℝ)/8) ≤ (997926004719761579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2177/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1626_exp_lower : (460057372864404137/500000000000000000 : ℝ) ≤ Real.exp ((-133211028957/200000000000 : ℝ)/8) ∧ Real.exp ((-133211028957/200000000000 : ℝ)/8) ≤ (36804589829152331/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133211028957/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1626_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054924723413/1000000000000 : ℝ) ≤ 4*Real.exp (17/128 : ℝ)*Real.exp (-mu (radius 8 (2177/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054924723413/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2177/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1626_exp_radius
  have hrNumeric : (983527980243/1000000000000 : ℝ) ≤ Real.exp (-2177/131072 : ℝ) ∧ Real.exp (-2177/131072 : ℝ) ≤ (245881995061/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983527980243/1000000000000 : ℝ) ≤ (radius 8 (2177/16384 : ℝ)) ∧ (radius 8 (2177/16384 : ℝ)) ≤ (245881995061/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2177/16384 : ℝ)) (983527980243/1000000000000 : ℝ) (245881995061/250000000000 : ℝ) (180755946173/1000000000000 : ℝ) (9037797309/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2177/16384 : ℝ)) (983527980243/1000000000000 : ℝ) (245881995061/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983527980243/1000000000000 : ℝ) (245881995061/250000000000 : ℝ) (991763990121/1000000000000 : ℝ) (495881995061/500000000000 : ℝ) (19834595839/20000000000 : ℝ) (61983111997/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 1 (991763990121/1000000000000 : ℝ) (495881995061/500000000000 : ℝ) (19834595839/20000000000 : ℝ) (61983111997/62500000000 : ℝ) (198349378207/200000000000 : ℝ) (991746891037/1000000000000 : ℝ) (123968361361/125000000000 : ℝ) (99174689089/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 2 (198349378207/200000000000 : ℝ) (991746891037/1000000000000 : ℝ) (123968361361/125000000000 : ℝ) (99174689089/100000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 3 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 4 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 5 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 6 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2177/16384 : ℝ)) 7 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2177/16384 : ℝ))) (180755946173/1000000000000 : ℝ) (9037797309/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180755946173/1000000000000 : ℝ) (9037797309/50000000000 : ℝ) (295188986543/500000000000 : ℝ) (59037797309/100000000000 : ℝ) (42515402641/100000000000 : ℝ) (425154026419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 1 (295188986543/500000000000 : ℝ) (59037797309/100000000000 : ℝ) (42515402641/100000000000 : ℝ) (425154026419/1000000000000 : ℝ) (126941499937/250000000000 : ℝ) (101553199951/200000000000 : ℝ) (250500285609/500000000000 : ℝ) (250500285613/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 2 (126941499937/250000000000 : ℝ) (101553199951/200000000000 : ℝ) (250500285609/500000000000 : ℝ) (250500285613/500000000000 : ℝ) (504383285483/1000000000000 : ℝ) (504383285491/1000000000000 : ℝ) (504371942041/1000000000000 : ℝ) (10087438841/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 3 (504383285483/1000000000000 : ℝ) (504383285491/1000000000000 : ℝ) (504371942041/1000000000000 : ℝ) (10087438841/20000000000 : ℝ) (252188806881/500000000000 : ℝ) (504377613771/1000000000000 : ℝ) (50437761373/100000000000 : ℝ) (504377613739/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 4 (252188806881/500000000000 : ℝ) (504377613771/1000000000000 : ℝ) (50437761373/100000000000 : ℝ) (504377613739/1000000000000 : ℝ) (252188806873/500000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 5 (252188806873/500000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 6 (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2177/16384 : ℝ))) 7 (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2177/16384 : ℝ)) hmem 8 (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2177/16384 : ℝ))) hcmem 8 (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2177/16384 : ℝ)) (991746890961/1000000000000 : ℝ) (247936722741/250000000000 : ℝ) (100875522749/200000000000 : ℝ) (100875522751/200000000000 : ℝ) (159773528953/200000000000 : ℝ) (159773528957/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1626_exp_lower
  have heNumeric : (2054924723413/1000000000000 : ℝ)/4 ≤ Real.exp (-133211028957/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054924723413/1000000000000 : ℝ)/4 ≤ Real.exp ((17/128 : ℝ)-(159773528957/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17/128 : ℝ) (2177/16384 : ℝ) (159773528957/200000000000 : ℝ) (2054924723413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1627; no trusted numerical premise.
theorem cover8_leaf1627_exp_radius : (997925053023815007/1000000000000000000 : ℝ) ≤ Real.exp ((-1089/65536 : ℝ)/8) ∧ Real.exp ((-1089/65536 : ℝ)/8) ≤ (31185157906994219/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1089/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1627_exp_lower : (460057467191889079/500000000000000000 : ℝ) ≤ Real.exp ((-2664214018047/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664214018047/4000000000000 : ℝ)/8) ≤ (920114934383778159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664214018047/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1627_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027464047027/500000000000 : ℝ) ≤ 4*Real.exp (2177/16384 : ℝ)*Real.exp (-mu (radius 8 (1089/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027464047027/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1089/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1627_exp_radius
  have hrNumeric : (983520476549/1000000000000 : ℝ) ≤ Real.exp (-1089/65536 : ℝ) ∧ Real.exp (-1089/65536 : ℝ) ≤ (19670409531/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983520476549/1000000000000 : ℝ) ≤ (radius 8 (1089/8192 : ℝ)) ∧ (radius 8 (1089/8192 : ℝ)) ≤ (19670409531/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1089/8192 : ℝ)) (983520476549/1000000000000 : ℝ) (19670409531/20000000000 : ℝ) (90398385227/500000000000 : ℝ) (180796770461/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1089/8192 : ℝ)) (983520476549/1000000000000 : ℝ) (19670409531/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983520476549/1000000000000 : ℝ) (19670409531/20000000000 : ℝ) (495880119137/500000000000 : ℝ) (39670409531/40000000000 : ℝ) (991726008809/1000000000000 : ℝ) (99172600881/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 1 (495880119137/500000000000 : ℝ) (39670409531/40000000000 : ℝ) (991726008809/1000000000000 : ℝ) (99172600881/100000000000 : ℝ) (991743123541/1000000000000 : ℝ) (991743123543/1000000000000 : ℝ) (991743123393/1000000000000 : ℝ) (198348624679/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 2 (991743123541/1000000000000 : ℝ) (991743123543/1000000000000 : ℝ) (991743123393/1000000000000 : ℝ) (198348624679/200000000000 : ℝ) (991743123467/1000000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 3 (991743123467/1000000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 4 (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 5 (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 6 (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1089/8192 : ℝ)) 7 (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1089/8192 : ℝ))) (90398385227/500000000000 : ℝ) (180796770461/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90398385227/500000000000 : ℝ) (180796770461/1000000000000 : ℝ) (590398385227/1000000000000 : ℝ) (590398385231/1000000000000 : ℝ) (85040406973/200000000000 : ℝ) (3401616279/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 1 (590398385227/1000000000000 : ℝ) (590398385231/1000000000000 : ℝ) (85040406973/200000000000 : ℝ) (3401616279/8000000000 : ℝ) (253900105023/500000000000 : ℝ) (507800210053/1000000000000 : ℝ) (100207503667/200000000000 : ℝ) (501037518343/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 2 (253900105023/500000000000 : ℝ) (507800210053/1000000000000 : ℝ) (100207503667/200000000000 : ℝ) (501037518343/1000000000000 : ℝ) (50441886419/100000000000 : ℝ) (252209432099/500000000000 : ℝ) (126101882681/250000000000 : ℝ) (126101882683/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 3 (50441886419/100000000000 : ℝ) (252209432099/500000000000 : ℝ) (126101882681/250000000000 : ℝ) (126101882683/250000000000 : ℝ) (504413197457/1000000000000 : ℝ) (100882639493/200000000000 : ℝ) (20176527897/40000000000 : ℝ) (252206598717/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 4 (504413197457/1000000000000 : ℝ) (100882639493/200000000000 : ℝ) (20176527897/40000000000 : ℝ) (252206598717/500000000000 : ℝ) (504413197441/1000000000000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 5 (504413197441/1000000000000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 6 (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1089/8192 : ℝ))) 7 (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1089/8192 : ℝ)) hmem 8 (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1089/8192 : ℝ))) hcmem 8 (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1089/8192 : ℝ)) (495871561733/500000000000 : ℝ) (991743123469/1000000000000 : ℝ) (788145621/1562500000 : ℝ) (10088263949/20000000000 : ℝ) (798927039649/1000000000000 : ℝ) (199731759917/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1627_exp_lower
  have heNumeric : (1027464047027/500000000000 : ℝ)/4 ≤ Real.exp (-2664214018047/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027464047027/500000000000 : ℝ)/4 ≤ Real.exp ((2177/16384 : ℝ)-(199731759917/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2177/16384 : ℝ) (1089/8192 : ℝ) (199731759917/250000000000 : ℝ) (1027464047027/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1628; no trusted numerical premise.
theorem cover8_leaf1628_exp_radius : (249481025332194011/250000000000000000 : ℝ) ≤ Real.exp ((-2179/131072 : ℝ)/8) ∧ Real.exp ((-2179/131072 : ℝ)/8) ≤ (199584820265755209/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2179/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1628_exp_lower : (5750719532245669/6250000000000000 : ℝ) ≤ Real.exp ((-1332103691603/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332103691603/2000000000000 : ℝ)/8) ≤ (920115125159307041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332103691603/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1628_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054931502587/1000000000000 : ℝ) ≤ 4*Real.exp (1089/8192 : ℝ)*Real.exp (-mu (radius 8 (2179/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054931502587/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2179/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1628_exp_radius
  have hrNumeric : (61469560807/62500000000 : ℝ) ≤ Real.exp (-2179/131072 : ℝ) ∧ Real.exp (-2179/131072 : ℝ) ≤ (983512972913/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61469560807/62500000000 : ℝ) ≤ (radius 8 (2179/16384 : ℝ)) ∧ (radius 8 (2179/16384 : ℝ)) ≤ (983512972913/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2179/16384 : ℝ)) (61469560807/62500000000 : ℝ) (983512972913/1000000000000 : ℝ) (90418792449/500000000000 : ℝ) (22604698113/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2179/16384 : ℝ)) (61469560807/62500000000 : ℝ) (983512972913/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61469560807/62500000000 : ℝ) (983512972913/1000000000000 : ℝ) (123969560807/125000000000 : ℝ) (991756486457/1000000000000 : ℝ) (495861112841/500000000000 : ℝ) (991722225683/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 1 (123969560807/125000000000 : ℝ) (991756486457/1000000000000 : ℝ) (495861112841/500000000000 : ℝ) (991722225683/1000000000000 : ℝ) (991739356069/1000000000000 : ℝ) (99173935607/100000000000 : ℝ) (991739355921/1000000000000 : ℝ) (991739355923/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 2 (991739356069/1000000000000 : ℝ) (99173935607/100000000000 : ℝ) (991739355921/1000000000000 : ℝ) (991739355923/1000000000000 : ℝ) (198347871199/200000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 3 (198347871199/200000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 4 (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 5 (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 6 (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2179/16384 : ℝ)) 7 (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2179/16384 : ℝ))) (90418792449/500000000000 : ℝ) (22604698113/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90418792449/500000000000 : ℝ) (22604698113/125000000000 : ℝ) (590418792449/1000000000000 : ℝ) (147604698113/250000000000 : ℝ) (85050005267/200000000000 : ℝ) (425250026343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 1 (590418792449/1000000000000 : ℝ) (147604698113/250000000000 : ℝ) (85050005267/200000000000 : ℝ) (425250026343/1000000000000 : ℝ) (31739650587/62500000000 : ℝ) (253917204699/500000000000 : ℝ) (501074452589/1000000000000 : ℝ) (125268613149/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 2 (31739650587/62500000000 : ℝ) (253917204699/500000000000 : ℝ) (501074452589/1000000000000 : ℝ) (125268613149/250000000000 : ℝ) (50445443099/100000000000 : ℝ) (504454430997/1000000000000 : ℝ) (504443107487/1000000000000 : ℝ) (100888621499/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 3 (50445443099/100000000000 : ℝ) (504454430997/1000000000000 : ℝ) (504443107487/1000000000000 : ℝ) (100888621499/200000000000 : ℝ) (252224384619/500000000000 : ℝ) (252224384623/500000000000 : ℝ) (252224384603/500000000000 : ℝ) (100889753843/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 4 (252224384619/500000000000 : ℝ) (252224384623/500000000000 : ℝ) (252224384603/500000000000 : ℝ) (100889753843/200000000000 : ℝ) (252224384611/500000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 5 (252224384611/500000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 6 (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2179/16384 : ℝ))) 7 (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2179/16384 : ℝ)) hmem 8 (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2179/16384 : ℝ))) hcmem 8 (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2179/16384 : ℝ)) (495869677997/500000000000 : ℝ) (991739355997/1000000000000 : ℝ) (504448769221/1000000000000 : ℝ) (504448769231/1000000000000 : ℝ) (159797283219/200000000000 : ℝ) (399493208057/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1628_exp_lower
  have heNumeric : (2054931502587/1000000000000 : ℝ)/4 ≤ Real.exp (-1332103691603/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054931502587/1000000000000 : ℝ)/4 ≤ Real.exp ((1089/8192 : ℝ)-(399493208057/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1089/8192 : ℝ) (2179/16384 : ℝ) (399493208057/500000000000 : ℝ) (2054931502587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1629; no trusted numerical premise.
theorem cover8_leaf1629_exp_radius : (997923149634644687/1000000000000000000 : ℝ) ≤ Real.exp ((-545/32768 : ℝ)/8) ∧ Real.exp ((-545/32768 : ℝ)/8) ≤ (62370196852165293/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-545/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1629_exp_lower : (92011531805355601/100000000000000000 : ℝ) ≤ Real.exp ((-2664200674681/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664200674681/4000000000000 : ℝ)/8) ≤ (920115318053556011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664200674681/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1629_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102746747449/50000000000 : ℝ) ≤ 4*Real.exp (2179/16384 : ℝ)*Real.exp (-mu (radius 8 (545/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (102746747449/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (545/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1629_exp_radius
  have hrNumeric : (245876367333/250000000000 : ℝ) ≤ Real.exp (-545/32768 : ℝ) ∧ Real.exp (-545/32768 : ℝ) ≤ (983505469333/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245876367333/250000000000 : ℝ) ≤ (radius 8 (545/4096 : ℝ)) ∧ (radius 8 (545/4096 : ℝ)) ≤ (983505469333/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (545/4096 : ℝ)) (245876367333/250000000000 : ℝ) (983505469333/1000000000000 : ℝ) (18087838951/100000000000 : ℝ) (180878389517/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (545/4096 : ℝ)) (245876367333/250000000000 : ℝ) (983505469333/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (545/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245876367333/250000000000 : ℝ) (983505469333/1000000000000 : ℝ) (495876367333/500000000000 : ℝ) (991752734667/1000000000000 : ℝ) (991718442569/1000000000000 : ℝ) (99171844257/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (545/4096 : ℝ)) 1 (495876367333/500000000000 : ℝ) (991752734667/1000000000000 : ℝ) (991718442569/1000000000000 : ℝ) (99171844257/100000000000 : ℝ) (991735588617/1000000000000 : ℝ) (991735588619/1000000000000 : ℝ) (991735588469/1000000000000 : ℝ) (991735588471/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (545/4096 : ℝ)) 2 (991735588617/1000000000000 : ℝ) (991735588619/1000000000000 : ℝ) (991735588469/1000000000000 : ℝ) (991735588471/1000000000000 : ℝ) (991735588543/1000000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (545/4096 : ℝ)) 3 (991735588543/1000000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (545/4096 : ℝ)) 4 (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (545/4096 : ℝ)) 5 (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (545/4096 : ℝ)) 6 (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (545/4096 : ℝ)) 7 (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (545/4096 : ℝ))) (18087838951/100000000000 : ℝ) (180878389517/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18087838951/100000000000 : ℝ) (180878389517/1000000000000 : ℝ) (118087838951/200000000000 : ℝ) (590439194759/1000000000000 : ℝ) (42529800083/100000000000 : ℝ) (425298000839/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 1 (118087838951/200000000000 : ℝ) (590439194759/1000000000000 : ℝ) (42529800083/100000000000 : ℝ) (425298000839/1000000000000 : ℝ) (15870893681/31250000000 : ℝ) (507868597799/1000000000000 : ℝ) (125277843497/250000000000 : ℝ) (125277843499/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 2 (15870893681/31250000000 : ℝ) (507868597799/1000000000000 : ℝ) (125277843497/250000000000 : ℝ) (125277843499/250000000000 : ℝ) (50448998589/100000000000 : ℝ) (252244992949/500000000000 : ℝ) (252239336169/500000000000 : ℝ) (504478672347/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 3 (50448998589/100000000000 : ℝ) (252244992949/500000000000 : ℝ) (252239336169/500000000000 : ℝ) (504478672347/1000000000000 : ℝ) (252242164557/500000000000 : ℝ) (504484329123/1000000000000 : ℝ) (252242164541/500000000000 : ℝ) (504484329091/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 4 (252242164557/500000000000 : ℝ) (504484329123/1000000000000 : ℝ) (252242164541/500000000000 : ℝ) (504484329091/1000000000000 : ℝ) (252242164549/500000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 5 (252242164549/500000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 6 (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (545/4096 : ℝ))) 7 (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (545/4096 : ℝ)) hmem 8 (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (545/4096 : ℝ))) hcmem 8 (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (545/4096 : ℝ)) (495867794271/500000000000 : ℝ) (198347117709/200000000000 : ℝ) (504484329097/1000000000000 : ℝ) (504484329107/1000000000000 : ℝ) (799045774119/1000000000000 : ℝ) (799045774139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1629_exp_lower
  have heNumeric : (102746747449/50000000000 : ℝ)/4 ≤ Real.exp (-2664200674681/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102746747449/50000000000 : ℝ)/4 ≤ Real.exp ((2179/16384 : ℝ)-(799045774139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2179/16384 : ℝ) (545/4096 : ℝ) (799045774139/1000000000000 : ℝ) (102746747449/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1630; no trusted numerical premise.
theorem cover8_leaf1630_exp_radius : (124740274742677617/125000000000000000 : ℝ) ≤ Real.exp ((-2181/131072 : ℝ)/8) ∧ Real.exp ((-2181/131072 : ℝ)/8) ≤ (997922197941420937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2181/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1630_exp_lower : (920115513065031211/1000000000000000000 : ℝ) ≤ Real.exp ((-666048473131/1000000000000 : ℝ)/8) ∧ Real.exp ((-666048473131/1000000000000 : ℝ)/8) ≤ (230028878266257803/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666048473131/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1630_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410987686641/200000000000 : ℝ) ≤ 4*Real.exp (545/4096 : ℝ)*Real.exp (-mu (radius 8 (2181/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410987686641/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2181/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1630_exp_radius
  have hrNumeric : (983497965809/1000000000000 : ℝ) ≤ Real.exp (-2181/131072 : ℝ) ∧ Real.exp (-2181/131072 : ℝ) ≤ (98349796581/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983497965809/1000000000000 : ℝ) ≤ (radius 8 (2181/16384 : ℝ)) ∧ (radius 8 (2181/16384 : ℝ)) ≤ (98349796581/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2181/16384 : ℝ)) (983497965809/1000000000000 : ℝ) (98349796581/100000000000 : ℝ) (180919184299/1000000000000 : ℝ) (36183836861/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2181/16384 : ℝ)) (983497965809/1000000000000 : ℝ) (98349796581/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983497965809/1000000000000 : ℝ) (98349796581/100000000000 : ℝ) (123968622863/125000000000 : ℝ) (198349796581/200000000000 : ℝ) (99171465947/100000000000 : ℝ) (61982166217/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 1 (123968622863/125000000000 : ℝ) (198349796581/200000000000 : ℝ) (99171465947/100000000000 : ℝ) (61982166217/62500000000 : ℝ) (991731821187/1000000000000 : ℝ) (991731821189/1000000000000 : ℝ) (495865910519/500000000000 : ℝ) (991731821041/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 2 (991731821187/1000000000000 : ℝ) (991731821189/1000000000000 : ℝ) (495865910519/500000000000 : ℝ) (991731821041/1000000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 3 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 4 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 5 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 6 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2181/16384 : ℝ)) 7 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2181/16384 : ℝ))) (180919184299/1000000000000 : ℝ) (36183836861/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180919184299/1000000000000 : ℝ) (36183836861/200000000000 : ℝ) (590459592149/1000000000000 : ℝ) (590459592153/1000000000000 : ℝ) (212672979183/500000000000 : ℝ) (212672979187/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 1 (590459592149/1000000000000 : ℝ) (590459592153/1000000000000 : ℝ) (212672979183/500000000000 : ℝ) (212672979187/500000000000 : ℝ) (507902775257/1000000000000 : ℝ) (15871961727/31250000000 : ℝ) (250574141273/500000000000 : ℝ) (501148282553/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 2 (507902775257/1000000000000 : ℝ) (15871961727/31250000000 : ℝ) (250574141273/500000000000 : ℝ) (501148282553/1000000000000 : ℝ) (504525528901/1000000000000 : ℝ) (504525528909/1000000000000 : ℝ) (50451422529/100000000000 : ℝ) (252257112649/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 3 (504525528901/1000000000000 : ℝ) (504525528909/1000000000000 : ℝ) (50451422529/100000000000 : ℝ) (252257112649/500000000000 : ℝ) (100903975419/200000000000 : ℝ) (31532492319/62500000000 : ℝ) (504519877063/1000000000000 : ℝ) (31532492317/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 4 (100903975419/200000000000 : ℝ) (31532492319/62500000000 : ℝ) (504519877063/1000000000000 : ℝ) (31532492317/62500000000 : ℝ) (504519877079/1000000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 5 (504519877079/1000000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 6 (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2181/16384 : ℝ))) 7 (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2181/16384 : ℝ)) hmem 8 (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2181/16384 : ℝ))) hcmem 8 (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2181/16384 : ℝ)) (123966477639/125000000000 : ℝ) (198346364223/200000000000 : ℝ) (252259938539/500000000000 : ℝ) (15766246159/31250000000 : ℝ) (799105113737/1000000000000 : ℝ) (199776278439/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1630_exp_lower
  have heNumeric : (410987686641/200000000000 : ℝ)/4 ≤ Real.exp (-666048473131/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410987686641/200000000000 : ℝ)/4 ≤ Real.exp ((545/4096 : ℝ)-(199776278439/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (545/4096 : ℝ) (2181/16384 : ℝ) (199776278439/250000000000 : ℝ) (410987686641/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1631; no trusted numerical premise.
theorem cover8_leaf1631_exp_radius : (99792124624910479/100000000000000000 : ℝ) ≤ Real.exp ((-1091/65536 : ℝ)/8) ∧ Real.exp ((-1091/65536 : ℝ)/8) ≤ (997921246249104791/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1091/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1631_exp_lower : (28753615943514651/31250000000000000 : ℝ) ≤ Real.exp ((-2664187036779/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664187036779/4000000000000 : ℝ)/8) ≤ (920115710192468833/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664187036779/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1631_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027470977621/500000000000 : ℝ) ≤ 4*Real.exp (2181/16384 : ℝ)*Real.exp (-mu (radius 8 (1091/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027470977621/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1091/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1631_exp_radius
  have hrNumeric : (122936307793/125000000000 : ℝ) ≤ Real.exp (-1091/65536 : ℝ) ∧ Real.exp (-1091/65536 : ℝ) ≤ (196698092469/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122936307793/125000000000 : ℝ) ≤ (radius 8 (1091/8192 : ℝ)) ∧ (radius 8 (1091/8192 : ℝ)) ≤ (196698092469/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1091/8192 : ℝ)) (122936307793/125000000000 : ℝ) (196698092469/200000000000 : ℝ) (36191993853/200000000000 : ℝ) (180959969271/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1091/8192 : ℝ)) (122936307793/125000000000 : ℝ) (196698092469/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122936307793/125000000000 : ℝ) (196698092469/200000000000 : ℝ) (247936307793/250000000000 : ℝ) (991745231173/1000000000000 : ℝ) (495855438193/500000000000 : ℝ) (247927719097/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 1 (247936307793/250000000000 : ℝ) (991745231173/1000000000000 : ℝ) (495855438193/500000000000 : ℝ) (247927719097/250000000000 : ℝ) (991728053779/1000000000000 : ℝ) (991728053781/1000000000000 : ℝ) (99172805363/100000000000 : ℝ) (7747875419/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 2 (991728053779/1000000000000 : ℝ) (991728053781/1000000000000 : ℝ) (99172805363/100000000000 : ℝ) (7747875419/7812500000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 3 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 4 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 5 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 6 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1091/8192 : ℝ)) 7 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1091/8192 : ℝ))) (36191993853/200000000000 : ℝ) (180959969271/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36191993853/200000000000 : ℝ) (180959969271/1000000000000 : ℝ) (73809998079/125000000000 : ℝ) (147619996159/250000000000 : ℝ) (425393898951/1000000000000 : ℝ) (425393898959/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 1 (73809998079/125000000000 : ℝ) (147619996159/250000000000 : ℝ) (425393898951/1000000000000 : ℝ) (425393898959/1000000000000 : ℝ) (507936941791/1000000000000 : ℝ) (253968470899/500000000000 : ℝ) (501185178267/1000000000000 : ℝ) (20047407131/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 2 (507936941791/1000000000000 : ℝ) (253968470899/500000000000 : ℝ) (501185178267/1000000000000 : ℝ) (20047407131/40000000000 : ℝ) (504561060029/1000000000000 : ℝ) (504561060037/1000000000000 : ℝ) (252274883173/500000000000 : ℝ) (252274883177/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 3 (504561060029/1000000000000 : ℝ) (504561060037/1000000000000 : ℝ) (252274883173/500000000000 : ℝ) (252274883177/500000000000 : ℝ) (504555413187/1000000000000 : ℝ) (126138853299/250000000000 : ℝ) (100911082631/200000000000 : ℝ) (126138853291/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 4 (504555413187/1000000000000 : ℝ) (126138853299/250000000000 : ℝ) (100911082631/200000000000 : ℝ) (126138853291/250000000000 : ℝ) (504555413171/1000000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 5 (504555413171/1000000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 6 (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1091/8192 : ℝ))) 7 (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1091/8192 : ℝ)) hmem 8 (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1091/8192 : ℝ))) hcmem 8 (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1091/8192 : ℝ)) (123966006713/125000000000 : ℝ) (991728053707/1000000000000 : ℝ) (50455541317/100000000000 : ℝ) (25227770659/50000000000 : ℝ) (799164434957/1000000000000 : ℝ) (24973888593/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1631_exp_lower
  have heNumeric : (1027470977621/500000000000 : ℝ)/4 ≤ Real.exp (-2664187036779/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027470977621/500000000000 : ℝ)/4 ≤ Real.exp ((2181/16384 : ℝ)-(24973888593/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2181/16384 : ℝ) (1091/8192 : ℝ) (24973888593/31250000000 : ℝ) (1027470977621/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1632; no trusted numerical premise.
theorem cover8_leaf1632_exp_radius : (124740036819712031/125000000000000000 : ℝ) ≤ Real.exp ((-2183/131072 : ℝ)/8) ∧ Real.exp ((-2183/131072 : ℝ)/8) ≤ (997920294557696249/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2183/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1632_exp_lower : (92011590943379997/100000000000000000 : ℝ) ≤ Real.exp ((-1332090053759/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332090053759/2000000000000 : ℝ)/8) ≤ (920115909433799971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332090053759/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1632_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513736378763/250000000000 : ℝ) ≤ 4*Real.exp (1091/8192 : ℝ)*Real.exp (-mu (radius 8 (2183/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513736378763/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2183/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1632_exp_radius
  have hrNumeric : (122935369867/125000000000 : ℝ) ≤ Real.exp (-2183/131072 : ℝ) ∧ Real.exp (-2183/131072 : ℝ) ≤ (983482958937/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122935369867/125000000000 : ℝ) ≤ (radius 8 (2183/16384 : ℝ)) ∧ (radius 8 (2183/16384 : ℝ)) ≤ (983482958937/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2183/16384 : ℝ)) (122935369867/125000000000 : ℝ) (983482958937/1000000000000 : ℝ) (181000744419/1000000000000 : ℝ) (90500372213/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2183/16384 : ℝ)) (122935369867/125000000000 : ℝ) (983482958937/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122935369867/125000000000 : ℝ) (983482958937/1000000000000 : ℝ) (247935369867/250000000000 : ℝ) (991741479469/1000000000000 : ℝ) (991707093317/1000000000000 : ℝ) (495853546659/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 1 (247935369867/250000000000 : ℝ) (991741479469/1000000000000 : ℝ) (991707093317/1000000000000 : ℝ) (495853546659/500000000000 : ℝ) (123965535799/125000000000 : ℝ) (495862143197/500000000000 : ℝ) (991724286243/1000000000000 : ℝ) (198344857249/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 2 (123965535799/125000000000 : ℝ) (495862143197/500000000000 : ℝ) (991724286243/1000000000000 : ℝ) (198344857249/200000000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 3 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 4 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 5 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 6 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2183/16384 : ℝ)) 7 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2183/16384 : ℝ))) (181000744419/1000000000000 : ℝ) (90500372213/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181000744419/1000000000000 : ℝ) (90500372213/500000000000 : ℝ) (590500372209/1000000000000 : ℝ) (590500372213/1000000000000 : ℝ) (212720911301/500000000000 : ℝ) (425441822611/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 1 (590500372209/1000000000000 : ℝ) (590500372213/1000000000000 : ℝ) (212720911301/500000000000 : ℝ) (425441822611/1000000000000 : ℝ) (101594219481/200000000000 : ℝ) (126992774353/250000000000 : ℝ) (250611030583/500000000000 : ℝ) (250611030587/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 2 (101594219481/200000000000 : ℝ) (126992774353/250000000000 : ℝ) (250611030583/500000000000 : ℝ) (250611030587/500000000000 : ℝ) (100919315857/200000000000 : ℝ) (504596579293/1000000000000 : ℝ) (504585295519/1000000000000 : ℝ) (504585295527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 3 (100919315857/200000000000 : ℝ) (504596579293/1000000000000 : ℝ) (504585295519/1000000000000 : ℝ) (504585295527/1000000000000 : ℝ) (252295468701/500000000000 : ℝ) (50459093741/100000000000 : ℝ) (50459093737/100000000000 : ℝ) (504590937379/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 4 (252295468701/500000000000 : ℝ) (50459093741/100000000000 : ℝ) (50459093737/100000000000 : ℝ) (504590937379/1000000000000 : ℝ) (252295468693/500000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 5 (252295468693/500000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 6 (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2183/16384 : ℝ))) 7 (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2183/16384 : ℝ)) hmem 8 (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2183/16384 : ℝ))) hcmem 8 (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2183/16384 : ℝ)) (991724286317/1000000000000 : ℝ) (12396553579/12500000000 : ℝ) (100918187477/200000000000 : ℝ) (100918187479/200000000000 : ℝ) (399611868899/500000000000 : ℝ) (799223737817/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1632_exp_lower
  have heNumeric : (513736378763/250000000000 : ℝ)/4 ≤ Real.exp (-1332090053759/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513736378763/250000000000 : ℝ)/4 ≤ Real.exp ((1091/8192 : ℝ)-(799223737817/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1091/8192 : ℝ) (2183/16384 : ℝ) (799223737817/1000000000000 : ℝ) (513736378763/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1633; no trusted numerical premise.
theorem cover8_leaf1633_exp_radius : (997919342867195309/1000000000000000000 : ℝ) ≤ Real.exp ((-273/16384 : ℝ)/8) ∧ Real.exp ((-273/16384 : ℝ)/8) ≤ (99791934286719531/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1633_exp_lower : (28753628462095961/31250000000000000 : ℝ) ≤ Real.exp ((-2664173104809/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664173104809/4000000000000 : ℝ)/8) ≤ (920116110787070753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664173104809/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1633_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027474556301/500000000000 : ℝ) ≤ 4*Real.exp (2183/16384 : ℝ)*Real.exp (-mu (radius 8 (273/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027474556301/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (273/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1633_exp_radius
  have hrNumeric : (196695091117/200000000000 : ℝ) ≤ Real.exp (-273/16384 : ℝ) ∧ Real.exp (-273/16384 : ℝ) ≤ (491737727793/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196695091117/200000000000 : ℝ) ≤ (radius 8 (273/2048 : ℝ)) ∧ (radius 8 (273/2048 : ℝ)) ≤ (491737727793/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (273/2048 : ℝ)) (196695091117/200000000000 : ℝ) (491737727793/500000000000 : ℝ) (18104150977/100000000000 : ℝ) (11315094361/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (273/2048 : ℝ)) (196695091117/200000000000 : ℝ) (491737727793/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (273/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196695091117/200000000000 : ℝ) (491737727793/500000000000 : ℝ) (61983607987/62500000000 : ℝ) (991737727793/1000000000000 : ℝ) (495851655131/500000000000 : ℝ) (991703310263/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (273/2048 : ℝ)) 1 (61983607987/62500000000 : ℝ) (991737727793/1000000000000 : ℝ) (495851655131/500000000000 : ℝ) (991703310263/1000000000000 : ℝ) (991720519027/1000000000000 : ℝ) (247930129757/250000000000 : ℝ) (991720518877/1000000000000 : ℝ) (991720518879/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (273/2048 : ℝ)) 2 (991720519027/1000000000000 : ℝ) (247930129757/250000000000 : ℝ) (991720518877/1000000000000 : ℝ) (991720518879/1000000000000 : ℝ) (123965064869/125000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (273/2048 : ℝ)) 3 (123965064869/125000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (273/2048 : ℝ)) 4 (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (273/2048 : ℝ)) 5 (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (273/2048 : ℝ)) 6 (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (273/2048 : ℝ)) 7 (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (273/2048 : ℝ))) (18104150977/100000000000 : ℝ) (11315094361/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18104150977/100000000000 : ℝ) (11315094361/62500000000 : ℝ) (118104150977/200000000000 : ℝ) (73815094361/125000000000 : ℝ) (85097945867/200000000000 : ℝ) (425489729343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 1 (118104150977/200000000000 : ℝ) (73815094361/125000000000 : ℝ) (85097945867/200000000000 : ℝ) (425489729343/1000000000000 : ℝ) (50800524211/100000000000 : ℝ) (127001310529/250000000000 : ℝ) (250629465627/500000000000 : ℝ) (501258931261/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 2 (50800524211/100000000000 : ℝ) (127001310529/250000000000 : ℝ) (250629465627/500000000000 : ℝ) (501258931261/1000000000000 : ℝ) (252316043341/500000000000 : ℝ) (504632086689/1000000000000 : ℝ) (25231040641/50000000000 : ℝ) (504620812827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 3 (252316043341/500000000000 : ℝ) (504632086689/1000000000000 : ℝ) (25231040641/50000000000 : ℝ) (504620812827/1000000000000 : ℝ) (504626449751/1000000000000 : ℝ) (252313224879/500000000000 : ℝ) (504626449719/1000000000000 : ℝ) (504626449727/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 4 (504626449751/1000000000000 : ℝ) (252313224879/500000000000 : ℝ) (504626449719/1000000000000 : ℝ) (504626449727/1000000000000 : ℝ) (100925289947/200000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 5 (100925289947/200000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 6 (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (273/2048 : ℝ))) 7 (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (273/2048 : ℝ)) hmem 8 (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (273/2048 : ℝ))) hcmem 8 (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (273/2048 : ℝ)) (991720518951/1000000000000 : ℝ) (495860259477/500000000000 : ℝ) (252313224867/500000000000 : ℝ) (504626449743/1000000000000 : ℝ) (799283022279/1000000000000 : ℝ) (99910377787/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1633_exp_lower
  have heNumeric : (1027474556301/500000000000 : ℝ)/4 ≤ Real.exp (-2664173104809/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027474556301/500000000000 : ℝ)/4 ≤ Real.exp ((2183/16384 : ℝ)-(99910377787/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2183/16384 : ℝ) (273/2048 : ℝ) (99910377787/125000000000 : ℝ) (1027474556301/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1634; no trusted numerical premise.
theorem cover8_leaf1634_exp_radius : (997918391177601973/1000000000000000000 : ℝ) ≤ Real.exp ((-2185/131072 : ℝ)/8) ∧ Real.exp ((-2185/131072 : ℝ)/8) ≤ (498959195588800987/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2185/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1634_exp_lower : (920116314250442333/1000000000000000000 : ℝ) ≤ Real.exp ((-666041507179/1000000000000 : ℝ)/8) ∧ Real.exp ((-666041507179/1000000000000 : ℝ)/8) ≤ (460058157125221167/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666041507179/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1634_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027476373929/500000000000 : ℝ) ≤ 4*Real.exp (273/2048 : ℝ)*Real.exp (-mu (radius 8 (2185/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027476373929/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2185/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1634_exp_radius
  have hrNumeric : (983467952291/1000000000000 : ℝ) ≤ Real.exp (-2185/131072 : ℝ) ∧ Real.exp (-2185/131072 : ℝ) ≤ (245866988073/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983467952291/1000000000000 : ℝ) ≤ (radius 8 (2185/16384 : ℝ)) ∧ (radius 8 (2185/16384 : ℝ)) ≤ (245866988073/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2185/16384 : ℝ)) (983467952291/1000000000000 : ℝ) (245866988073/250000000000 : ℝ) (181082265323/1000000000000 : ℝ) (181082265329/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2185/16384 : ℝ)) (983467952291/1000000000000 : ℝ) (245866988073/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983467952291/1000000000000 : ℝ) (245866988073/250000000000 : ℝ) (198346795229/200000000000 : ℝ) (495866988073/500000000000 : ℝ) (991699527221/1000000000000 : ℝ) (495849763611/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 1 (198346795229/200000000000 : ℝ) (495866988073/500000000000 : ℝ) (991699527221/1000000000000 : ℝ) (495849763611/500000000000 : ℝ) (991716751683/1000000000000 : ℝ) (247929187921/250000000000 : ℝ) (991716751533/1000000000000 : ℝ) (198343350307/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 2 (991716751683/1000000000000 : ℝ) (247929187921/250000000000 : ℝ) (991716751533/1000000000000 : ℝ) (198343350307/200000000000 : ℝ) (123964593951/125000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 3 (123964593951/125000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 4 (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 5 (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 6 (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2185/16384 : ℝ)) 7 (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2185/16384 : ℝ))) (181082265323/1000000000000 : ℝ) (181082265329/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181082265323/1000000000000 : ℝ) (181082265329/1000000000000 : ℝ) (590541132661/1000000000000 : ℝ) (118108226533/200000000000 : ℝ) (425537619163/1000000000000 : ℝ) (425537619171/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 1 (590541132661/1000000000000 : ℝ) (118108226533/200000000000 : ℝ) (425537619163/1000000000000 : ℝ) (425537619171/1000000000000 : ℝ) (63504921989/125000000000 : ℝ) (254019687959/500000000000 : ℝ) (250647894271/500000000000 : ℝ) (501295788549/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 2 (63504921989/125000000000 : ℝ) (254019687959/500000000000 : ℝ) (250647894271/500000000000 : ℝ) (501295788549/1000000000000 : ℝ) (504667582227/1000000000000 : ℝ) (252333791117/500000000000 : ℝ) (252328159129/500000000000 : ℝ) (100931263653/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 3 (504667582227/1000000000000 : ℝ) (252333791117/500000000000 : ℝ) (252328159129/500000000000 : ℝ) (100931263653/200000000000 : ℝ) (252330975121/500000000000 : ℝ) (2018647801/4000000000 : ℝ) (504661950211/1000000000000 : ℝ) (504661950219/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 4 (252330975121/500000000000 : ℝ) (2018647801/4000000000 : ℝ) (504661950211/1000000000000 : ℝ) (504661950219/1000000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 5 (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 6 (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2185/16384 : ℝ))) 7 (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2185/16384 : ℝ)) hmem 8 (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2185/16384 : ℝ))) hcmem 8 (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2185/16384 : ℝ)) (991716751607/1000000000000 : ℝ) (99171675161/100000000000 : ℝ) (252330975113/500000000000 : ℝ) (100932390047/200000000000 : ℝ) (799342288411/1000000000000 : ℝ) (799342288429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1634_exp_lower
  have heNumeric : (1027476373929/500000000000 : ℝ)/4 ≤ Real.exp (-666041507179/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027476373929/500000000000 : ℝ)/4 ≤ Real.exp ((273/2048 : ℝ)-(799342288429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (273/2048 : ℝ) (2185/16384 : ℝ) (799342288429/1000000000000 : ℝ) (1027476373929/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1635; no trusted numerical premise.
theorem cover8_leaf1635_exp_radius : (498958719744458119/500000000000000000 : ℝ) ≤ Real.exp ((-1093/65536 : ℝ)/8) ∧ Real.exp ((-1093/65536 : ℝ)/8) ≤ (997917439488916239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1635_exp_lower : (460058259911728027/500000000000000000 : ℝ) ≤ Real.exp ((-532831775851/800000000000 : ℝ)/8) ∧ Real.exp ((-532831775851/800000000000 : ℝ)/8) ≤ (184023303964691211/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532831775851/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1635_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513739105203/250000000000 : ℝ) ≤ 4*Real.exp (2185/16384 : ℝ)*Real.exp (-mu (radius 8 (1093/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (513739105203/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1093/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1635_exp_radius
  have hrNumeric : (196692089811/200000000000 : ℝ) ≤ Real.exp (-1093/65536 : ℝ) ∧ Real.exp (-1093/65536 : ℝ) ≤ (30733139033/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196692089811/200000000000 : ℝ) ≤ (radius 8 (1093/8192 : ℝ)) ∧ (radius 8 (1093/8192 : ℝ)) ≤ (30733139033/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1093/8192 : ℝ)) (196692089811/200000000000 : ℝ) (30733139033/31250000000 : ℝ) (181123011079/1000000000000 : ℝ) (90561505543/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1093/8192 : ℝ)) (196692089811/200000000000 : ℝ) (30733139033/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196692089811/200000000000 : ℝ) (30733139033/31250000000 : ℝ) (991730224527/1000000000000 : ℝ) (61983139033/62500000000 : ℝ) (198339148839/200000000000 : ℝ) (247923936049/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 1 (991730224527/1000000000000 : ℝ) (61983139033/62500000000 : ℝ) (198339148839/200000000000 : ℝ) (247923936049/250000000000 : ℝ) (991712984361/1000000000000 : ℝ) (495856492181/500000000000 : ℝ) (991712984211/1000000000000 : ℝ) (991712984213/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 2 (991712984361/1000000000000 : ℝ) (495856492181/500000000000 : ℝ) (991712984211/1000000000000 : ℝ) (991712984213/1000000000000 : ℝ) (495856492143/500000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 3 (495856492143/500000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 4 (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 5 (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 6 (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1093/8192 : ℝ)) 7 (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1093/8192 : ℝ))) (181123011079/1000000000000 : ℝ) (90561505543/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181123011079/1000000000000 : ℝ) (90561505543/500000000000 : ℝ) (590561505539/1000000000000 : ℝ) (590561505543/1000000000000 : ℝ) (425585492091/1000000000000 : ℝ) (425585492101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 1 (590561505539/1000000000000 : ℝ) (590561505543/1000000000000 : ℝ) (425585492091/1000000000000 : ℝ) (425585492101/1000000000000 : ℝ) (101614699763/200000000000 : ℝ) (254036749411/500000000000 : ℝ) (250666316517/500000000000 : ℝ) (250666316521/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 2 (101614699763/200000000000 : ℝ) (254036749411/500000000000 : ℝ) (250666316517/500000000000 : ℝ) (250666316521/500000000000 : ℝ) (126175766481/250000000000 : ℝ) (126175766483/250000000000 : ℝ) (504691811837/1000000000000 : ℝ) (100938362369/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 3 (126175766481/250000000000 : ℝ) (126175766483/250000000000 : ℝ) (504691811837/1000000000000 : ℝ) (100938362369/200000000000 : ℝ) (3154358993/6250000000 : ℝ) (504697438889/1000000000000 : ℝ) (504697438849/1000000000000 : ℝ) (252348719429/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 4 (3154358993/6250000000 : ℝ) (504697438889/1000000000000 : ℝ) (504697438849/1000000000000 : ℝ) (252348719429/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 5 (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 6 (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1093/8192 : ℝ))) 7 (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1093/8192 : ℝ)) hmem 8 (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1093/8192 : ℝ))) hcmem 8 (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1093/8192 : ℝ)) (198342596857/200000000000 : ℝ) (30991030759/31250000000 : ℝ) (31543589929/62500000000 : ℝ) (252348719437/500000000000 : ℝ) (799401536201/1000000000000 : ℝ) (39970076811/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1635_exp_lower
  have heNumeric : (513739105203/250000000000 : ℝ)/4 ≤ Real.exp (-532831775851/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513739105203/250000000000 : ℝ)/4 ≤ Real.exp ((2185/16384 : ℝ)-(39970076811/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2185/16384 : ℝ) (1093/8192 : ℝ) (39970076811/50000000000 : ℝ) (513739105203/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1636; no trusted numerical premise.
theorem cover8_leaf1636_exp_radius : (997916487801138103/1000000000000000000 : ℝ) ≤ Real.exp ((-2187/131072 : ℝ)/8) ∧ Real.exp ((-2187/131072 : ℝ)/8) ≤ (124739560975142263/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1636_exp_lower : (920116727503467993/1000000000000000000 : ℝ) ≤ Real.exp ((-1332075828259/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332075828259/2000000000000 : ℝ)/8) ≤ (460058363751733997/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332075828259/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1636_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027480065709/500000000000 : ℝ) ≤ 4*Real.exp (1093/8192 : ℝ)*Real.exp (-mu (radius 8 (2187/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027480065709/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2187/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1636_exp_radius
  have hrNumeric : (245863236469/250000000000 : ℝ) ≤ Real.exp (-2187/131072 : ℝ) ∧ Real.exp (-2187/131072 : ℝ) ≤ (983452945877/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245863236469/250000000000 : ℝ) ≤ (radius 8 (2187/16384 : ℝ)) ∧ (radius 8 (2187/16384 : ℝ)) ≤ (983452945877/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2187/16384 : ℝ)) (245863236469/250000000000 : ℝ) (983452945877/1000000000000 : ℝ) (181163747051/1000000000000 : ℝ) (90581873529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2187/16384 : ℝ)) (245863236469/250000000000 : ℝ) (983452945877/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245863236469/250000000000 : ℝ) (983452945877/1000000000000 : ℝ) (495863236469/500000000000 : ℝ) (991726472939/1000000000000 : ℝ) (991691961183/1000000000000 : ℝ) (198338392237/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 1 (495863236469/500000000000 : ℝ) (991726472939/1000000000000 : ℝ) (991691961183/1000000000000 : ℝ) (198338392237/200000000000 : ℝ) (49585460853/50000000000 : ℝ) (495854608531/500000000000 : ℝ) (99170921691/100000000000 : ℝ) (61981826057/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 2 (49585460853/50000000000 : ℝ) (495854608531/500000000000 : ℝ) (99170921691/100000000000 : ℝ) (61981826057/62500000000 : ℝ) (198341843397/200000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 3 (198341843397/200000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 4 (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 5 (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 6 (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2187/16384 : ℝ)) 7 (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2187/16384 : ℝ))) (181163747051/1000000000000 : ℝ) (90581873529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181163747051/1000000000000 : ℝ) (90581873529/500000000000 : ℝ) (23623274941/40000000000 : ℝ) (590581873529/1000000000000 : ℝ) (212816674071/500000000000 : ℝ) (425633348151/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 1 (23623274941/40000000000 : ℝ) (590581873529/1000000000000 : ℝ) (212816674071/500000000000 : ℝ) (425633348151/1000000000000 : ℝ) (508107610833/1000000000000 : ℝ) (12702690271/25000000000 : ℝ) (250684732373/500000000000 : ℝ) (250684732377/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 2 (508107610833/1000000000000 : ℝ) (12702690271/25000000000 : ℝ) (250684732373/500000000000 : ℝ) (250684732377/500000000000 : ℝ) (504738537789/1000000000000 : ℝ) (504738537797/1000000000000 : ℝ) (126181823393/250000000000 : ℝ) (25236364679/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 3 (504738537789/1000000000000 : ℝ) (504738537797/1000000000000 : ℝ) (126181823393/250000000000 : ℝ) (25236364679/50000000000 : ℝ) (3154580723/6250000000 : ℝ) (504732915689/1000000000000 : ℝ) (504732915649/1000000000000 : ℝ) (252366457829/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 4 (3154580723/6250000000 : ℝ) (504732915689/1000000000000 : ℝ) (504732915649/1000000000000 : ℝ) (252366457829/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 5 (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 6 (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2187/16384 : ℝ))) 7 (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2187/16384 : ℝ)) hmem 8 (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2187/16384 : ℝ))) hcmem 8 (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2187/16384 : ℝ)) (123963652123/125000000000 : ℝ) (991709216987/1000000000000 : ℝ) (31545807229/62500000000 : ℝ) (252366457837/500000000000 : ℝ) (799460765673/1000000000000 : ℝ) (199865191423/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1636_exp_lower
  have heNumeric : (1027480065709/500000000000 : ℝ)/4 ≤ Real.exp (-1332075828259/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027480065709/500000000000 : ℝ)/4 ≤ Real.exp ((1093/8192 : ℝ)-(199865191423/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1093/8192 : ℝ) (2187/16384 : ℝ) (199865191423/250000000000 : ℝ) (1027480065709/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1637; no trusted numerical premise.
theorem cover8_leaf1637_exp_radius : (997915536114267569/1000000000000000000 : ℝ) ≤ Real.exp ((-547/32768 : ℝ)/8) ∧ Real.exp ((-547/32768 : ℝ)/8) ≤ (99791553611426757/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-547/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1637_exp_lower : (920116937288639343/1000000000000000000 : ℝ) ≤ Real.exp ((-2664144360569/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664144360569/4000000000000 : ℝ)/8) ≤ (57507308580539959/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664144360569/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1637_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027481939821/500000000000 : ℝ) ≤ 4*Real.exp (2187/16384 : ℝ)*Real.exp (-mu (radius 8 (547/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027481939821/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (547/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1637_exp_radius
  have hrNumeric : (491722721377/500000000000 : ℝ) ≤ Real.exp (-547/32768 : ℝ) ∧ Real.exp (-547/32768 : ℝ) ≤ (196689088551/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491722721377/500000000000 : ℝ) ≤ (radius 8 (547/4096 : ℝ)) ∧ (radius 8 (547/4096 : ℝ)) ≤ (196689088551/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (547/4096 : ℝ)) (491722721377/500000000000 : ℝ) (196689088551/200000000000 : ℝ) (90602236623/500000000000 : ℝ) (45301118313/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (547/4096 : ℝ)) (491722721377/500000000000 : ℝ) (196689088551/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (547/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491722721377/500000000000 : ℝ) (196689088551/200000000000 : ℝ) (991722721377/1000000000000 : ℝ) (495861360689/500000000000 : ℝ) (495844089093/500000000000 : ℝ) (991688178187/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (547/4096 : ℝ)) 1 (991722721377/1000000000000 : ℝ) (495861360689/500000000000 : ℝ) (495844089093/500000000000 : ℝ) (991688178187/1000000000000 : ℝ) (991705449781/1000000000000 : ℝ) (991705449783/1000000000000 : ℝ) (991705449631/1000000000000 : ℝ) (991705449633/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (547/4096 : ℝ)) 2 (991705449781/1000000000000 : ℝ) (991705449783/1000000000000 : ℝ) (991705449631/1000000000000 : ℝ) (991705449633/1000000000000 : ℝ) (495852724853/500000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (547/4096 : ℝ)) 3 (495852724853/500000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (547/4096 : ℝ)) 4 (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (547/4096 : ℝ)) 5 (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (547/4096 : ℝ)) 6 (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (547/4096 : ℝ)) 7 (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (547/4096 : ℝ))) (90602236623/500000000000 : ℝ) (45301118313/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90602236623/500000000000 : ℝ) (45301118313/250000000000 : ℝ) (590602236623/1000000000000 : ℝ) (295301118313/500000000000 : ℝ) (425681187329/1000000000000 : ℝ) (425681187337/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 1 (590602236623/1000000000000 : ℝ) (295301118313/500000000000 : ℝ) (425681187329/1000000000000 : ℝ) (425681187337/1000000000000 : ℝ) (63517713997/125000000000 : ℝ) (254070855991/500000000000 : ℝ) (501406283691/1000000000000 : ℝ) (250703141849/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 2 (63517713997/125000000000 : ℝ) (254070855991/500000000000 : ℝ) (501406283691/1000000000000 : ℝ) (250703141849/500000000000 : ℝ) (504773997833/1000000000000 : ℝ) (6309674973/12500000000 : ℝ) (252381381737/500000000000 : ℝ) (504762763481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 3 (504773997833/1000000000000 : ℝ) (6309674973/12500000000 : ℝ) (252381381737/500000000000 : ℝ) (504762763481/1000000000000 : ℝ) (504768380653/1000000000000 : ℝ) (504768380661/1000000000000 : ℝ) (252384190311/500000000000 : ℝ) (50476838063/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 4 (504768380653/1000000000000 : ℝ) (504768380661/1000000000000 : ℝ) (252384190311/500000000000 : ℝ) (50476838063/100000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 5 (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 6 (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (547/4096 : ℝ))) 7 (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (547/4096 : ℝ)) hmem 8 (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (547/4096 : ℝ))) hcmem 8 (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (547/4096 : ℝ)) (198341089941/200000000000 : ℝ) (247926362427/250000000000 : ℝ) (504768380637/1000000000000 : ℝ) (252384190323/500000000000 : ℝ) (199879994211/250000000000 : ℝ) (799519976861/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1637_exp_lower
  have heNumeric : (1027481939821/500000000000 : ℝ)/4 ≤ Real.exp (-2664144360569/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027481939821/500000000000 : ℝ)/4 ≤ Real.exp ((2187/16384 : ℝ)-(799519976861/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2187/16384 : ℝ) (547/4096 : ℝ) (799519976861/1000000000000 : ℝ) (1027481939821/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1638; no trusted numerical premise.
theorem cover8_leaf1638_exp_radius : (997914584428304633/1000000000000000000 : ℝ) ≤ Real.exp ((-2189/131072 : ℝ)/8) ∧ Real.exp ((-2189/131072 : ℝ)/8) ≤ (498957292214152317/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2189/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1638_exp_lower : (36804685967089853/40000000000000000 : ℝ) ≤ Real.exp ((-666034247867/1000000000000 : ℝ)/8) ∧ Real.exp ((-666034247867/1000000000000 : ℝ)/8) ≤ (460058574588623163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666034247867/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1638_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410993533091/200000000000 : ℝ) ≤ 4*Real.exp (547/4096 : ℝ)*Real.exp (-mu (radius 8 (2189/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410993533091/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2189/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1638_exp_radius
  have hrNumeric : (983437939689/1000000000000 : ℝ) ≤ Real.exp (-2189/131072 : ℝ) ∧ Real.exp (-2189/131072 : ℝ) ≤ (98343793969/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983437939689/1000000000000 : ℝ) ≤ (radius 8 (2189/16384 : ℝ)) ∧ (radius 8 (2189/16384 : ℝ)) ≤ (98343793969/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2189/16384 : ℝ)) (983437939689/1000000000000 : ℝ) (98343793969/100000000000 : ℝ) (181245189669/1000000000000 : ℝ) (7249807587/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2189/16384 : ℝ)) (983437939689/1000000000000 : ℝ) (98343793969/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983437939689/1000000000000 : ℝ) (98343793969/100000000000 : ℝ) (247929742461/250000000000 : ℝ) (198343793969/200000000000 : ℝ) (495842197601/500000000000 : ℝ) (247921098801/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 1 (247929742461/250000000000 : ℝ) (198343793969/200000000000 : ℝ) (495842197601/500000000000 : ℝ) (247921098801/250000000000 : ℝ) (991701682523/1000000000000 : ℝ) (39668067301/40000000000 : ℝ) (247925420593/250000000000 : ℝ) (495850841187/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 2 (991701682523/1000000000000 : ℝ) (39668067301/40000000000 : ℝ) (247925420593/250000000000 : ℝ) (495850841187/500000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 3 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 4 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 5 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 6 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2189/16384 : ℝ)) 7 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2189/16384 : ℝ))) (181245189669/1000000000000 : ℝ) (7249807587/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181245189669/1000000000000 : ℝ) (7249807587/40000000000 : ℝ) (295311297417/500000000000 : ℝ) (295311297419/500000000000 : ℝ) (425729009663/1000000000000 : ℝ) (425729009671/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 1 (295311297417/500000000000 : ℝ) (295311297419/500000000000 : ℝ) (425729009663/1000000000000 : ℝ) (425729009671/1000000000000 : ℝ) (63521975281/125000000000 : ℝ) (101635160451/200000000000 : ℝ) (250721544937/500000000000 : ℝ) (250721544941/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 2 (63521975281/125000000000 : ℝ) (101635160451/200000000000 : ℝ) (250721544937/500000000000 : ℝ) (250721544941/500000000000 : ℝ) (504809446061/1000000000000 : ℝ) (504809446069/1000000000000 : ℝ) (126199555387/250000000000 : ℝ) (126199555389/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 3 (504809446061/1000000000000 : ℝ) (504809446069/1000000000000 : ℝ) (126199555387/250000000000 : ℝ) (126199555389/250000000000 : ℝ) (126200958451/250000000000 : ℝ) (504803833813/1000000000000 : ℝ) (504803833773/1000000000000 : ℝ) (252401916891/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 4 (126200958451/250000000000 : ℝ) (504803833813/1000000000000 : ℝ) (504803833773/1000000000000 : ℝ) (252401916891/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 5 (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 6 (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2189/16384 : ℝ))) 7 (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2189/16384 : ℝ)) hmem 8 (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2189/16384 : ℝ))) hcmem 8 (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2189/16384 : ℝ)) (991701682447/1000000000000 : ℝ) (19834033649/20000000000 : ℝ) (126200958447/250000000000 : ℝ) (252401916899/500000000000 : ℝ) (399789584861/500000000000 : ℝ) (399789584871/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1638_exp_lower
  have heNumeric : (410993533091/200000000000 : ℝ)/4 ≤ Real.exp (-666034247867/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410993533091/200000000000 : ℝ)/4 ≤ Real.exp ((547/4096 : ℝ)-(399789584871/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (547/4096 : ℝ) (2189/16384 : ℝ) (399789584871/500000000000 : ℝ) (410993533091/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1639; no trusted numerical premise.
theorem cover8_leaf1639_exp_radius : (62369602046453081/62500000000000000 : ℝ) ≤ Real.exp ((-1095/65536 : ℝ)/8) ∧ Real.exp ((-1095/65536 : ℝ)/8) ≤ (997913632743249297/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1095/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1639_exp_lower : (920117363168715317/1000000000000000000 : ℝ) ≤ Real.exp ((-532825909847/800000000000 : ℝ)/8) ∧ Real.exp ((-532825909847/800000000000 : ℝ)/8) ≤ (460058681584357659/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532825909847/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1639_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027485744423/500000000000 : ℝ) ≤ 4*Real.exp (2189/16384 : ℝ)*Real.exp (-mu (radius 8 (1095/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027485744423/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1095/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1639_exp_radius
  have hrNumeric : (491715218341/500000000000 : ℝ) ≤ Real.exp (-1095/65536 : ℝ) ∧ Real.exp (-1095/65536 : ℝ) ≤ (983430436683/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491715218341/500000000000 : ℝ) ≤ (radius 8 (1095/8192 : ℝ)) ∧ (radius 8 (1095/8192 : ℝ)) ≤ (983430436683/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1095/8192 : ℝ)) (491715218341/500000000000 : ℝ) (983430436683/1000000000000 : ℝ) (90642948161/500000000000 : ℝ) (181285896329/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1095/8192 : ℝ)) (491715218341/500000000000 : ℝ) (983430436683/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491715218341/500000000000 : ℝ) (983430436683/1000000000000 : ℝ) (991715218341/1000000000000 : ℝ) (495857609171/500000000000 : ℝ) (495840306117/500000000000 : ℝ) (247920153059/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 1 (991715218341/1000000000000 : ℝ) (495857609171/500000000000 : ℝ) (495840306117/500000000000 : ℝ) (247920153059/250000000000 : ℝ) (991697915287/1000000000000 : ℝ) (991697915289/1000000000000 : ℝ) (3873819981/3906250000 : ℝ) (991697915139/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 2 (991697915287/1000000000000 : ℝ) (991697915289/1000000000000 : ℝ) (3873819981/3906250000 : ℝ) (991697915139/1000000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 3 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 4 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 5 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 6 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1095/8192 : ℝ)) 7 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1095/8192 : ℝ))) (90642948161/500000000000 : ℝ) (181285896329/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90642948161/500000000000 : ℝ) (181285896329/1000000000000 : ℝ) (590642948161/1000000000000 : ℝ) (118128589633/200000000000 : ℝ) (425776815153/1000000000000 : ℝ) (212888407581/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 1 (590642948161/1000000000000 : ℝ) (118128589633/200000000000 : ℝ) (425776815153/1000000000000 : ℝ) (212888407581/500000000000 : ℝ) (508209881657/1000000000000 : ℝ) (7940779401/15625000000 : ℝ) (100295976661/200000000000 : ℝ) (501479883313/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 2 (508209881657/1000000000000 : ℝ) (7940779401/15625000000 : ℝ) (100295976661/200000000000 : ℝ) (501479883313/1000000000000 : ℝ) (504844882481/1000000000000 : ℝ) (504844882489/1000000000000 : ℝ) (504833667803/1000000000000 : ℝ) (504833667811/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 3 (504844882481/1000000000000 : ℝ) (504844882489/1000000000000 : ℝ) (504833667803/1000000000000 : ℝ) (504833667811/1000000000000 : ℝ) (252419637571/500000000000 : ℝ) (10096785503/20000000000 : ℝ) (50483927511/100000000000 : ℝ) (504839275119/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 4 (252419637571/500000000000 : ℝ) (10096785503/20000000000 : ℝ) (50483927511/100000000000 : ℝ) (504839275119/1000000000000 : ℝ) (252419637563/500000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 5 (252419637563/500000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 6 (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1095/8192 : ℝ))) 7 (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1095/8192 : ℝ)) hmem 8 (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1095/8192 : ℝ))) hcmem 8 (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1095/8192 : ℝ)) (991697915211/1000000000000 : ℝ) (495848957607/500000000000 : ℝ) (4038714201/8000000000 : ℝ) (100967855027/200000000000 : ℝ) (1249434913/1562500000 : ℝ) (39981917217/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1639_exp_lower
  have heNumeric : (1027485744423/500000000000 : ℝ)/4 ≤ Real.exp (-532825909847/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027485744423/500000000000 : ℝ)/4 ≤ Real.exp ((2189/16384 : ℝ)-(39981917217/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2189/16384 : ℝ) (1095/8192 : ℝ) (39981917217/50000000000 : ℝ) (1027485744423/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1640; no trusted numerical premise.
theorem cover8_leaf1640_exp_radius : (199582536211820311/200000000000000000 : ℝ) ≤ Real.exp ((-2191/131072 : ℝ)/8) ∧ Real.exp ((-2191/131072 : ℝ)/8) ≤ (249478170264775389/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2191/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1640_exp_lower : (18402351585208049/20000000000000000 : ℝ) ≤ Real.exp ((-1332061016981/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332061016981/2000000000000 : ℝ)/8) ≤ (920117579260402451/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332061016981/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1640_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054975349767/1000000000000 : ℝ) ≤ 4*Real.exp (1095/8192 : ℝ)*Real.exp (-mu (radius 8 (2191/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054975349767/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2191/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1640_exp_radius
  have hrNumeric : (245855733433/250000000000 : ℝ) ≤ Real.exp (-2191/131072 : ℝ) ∧ Real.exp (-2191/131072 : ℝ) ≤ (983422933733/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245855733433/250000000000 : ℝ) ≤ (radius 8 (2191/16384 : ℝ)) ∧ (radius 8 (2191/16384 : ℝ)) ≤ (983422933733/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2191/16384 : ℝ)) (245855733433/250000000000 : ℝ) (983422933733/1000000000000 : ℝ) (181326593217/1000000000000 : ℝ) (22665824153/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2191/16384 : ℝ)) (245855733433/250000000000 : ℝ) (983422933733/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245855733433/250000000000 : ℝ) (983422933733/1000000000000 : ℝ) (495855733433/500000000000 : ℝ) (991711466867/1000000000000 : ℝ) (6197980183/6250000000 : ℝ) (495838414641/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 1 (495855733433/500000000000 : ℝ) (991711466867/1000000000000 : ℝ) (6197980183/6250000000 : ℝ) (495838414641/500000000000 : ℝ) (991694148073/1000000000000 : ℝ) (39667765923/40000000000 : ℝ) (991694147921/1000000000000 : ℝ) (247923536981/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 2 (991694148073/1000000000000 : ℝ) (39667765923/40000000000 : ℝ) (991694147921/1000000000000 : ℝ) (247923536981/250000000000 : ℝ) (991694147997/1000000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 3 (991694147997/1000000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 4 (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 5 (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 6 (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2191/16384 : ℝ)) 7 (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2191/16384 : ℝ))) (181326593217/1000000000000 : ℝ) (22665824153/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181326593217/1000000000000 : ℝ) (22665824153/125000000000 : ℝ) (18458228019/31250000000 : ℝ) (147665824153/250000000000 : ℝ) (212912301909/500000000000 : ℝ) (425824603827/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 1 (18458228019/31250000000 : ℝ) (147665824153/250000000000 : ℝ) (212912301909/500000000000 : ℝ) (425824603827/1000000000000 : ℝ) (508243950213/1000000000000 : ℝ) (25412197511/50000000000 : ℝ) (250758331999/500000000000 : ℝ) (250758332003/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 2 (508243950213/1000000000000 : ℝ) (25412197511/50000000000 : ℝ) (250758331999/500000000000 : ℝ) (250758332003/500000000000 : ℝ) (100976061421/200000000000 : ℝ) (504880307113/1000000000000 : ℝ) (504869102251/1000000000000 : ℝ) (504869102259/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 3 (100976061421/200000000000 : ℝ) (504880307113/1000000000000 : ℝ) (504869102251/1000000000000 : ℝ) (504869102259/1000000000000 : ℝ) (252437352339/500000000000 : ℝ) (252437352343/500000000000 : ℝ) (252437352323/500000000000 : ℝ) (100974940931/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 4 (252437352339/500000000000 : ℝ) (252437352343/500000000000 : ℝ) (252437352323/500000000000 : ℝ) (100974940931/200000000000 : ℝ) (252437352331/500000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 5 (252437352331/500000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 6 (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2191/16384 : ℝ))) 7 (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2191/16384 : ℝ)) hmem 8 (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2191/16384 : ℝ))) hcmem 8 (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2191/16384 : ℝ)) (247923536999/250000000000 : ℝ) (247923537/250000000 : ℝ) (504874704661/1000000000000 : ℝ) (504874704671/1000000000000 : ℝ) (399848750329/500000000000 : ℝ) (399848750339/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1640_exp_lower
  have heNumeric : (2054975349767/1000000000000 : ℝ)/4 ≤ Real.exp (-1332061016981/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054975349767/1000000000000 : ℝ)/4 ≤ Real.exp ((1095/8192 : ℝ)-(399848750339/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1095/8192 : ℝ) (2191/16384 : ℝ) (399848750339/500000000000 : ℝ) (2054975349767/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1641; no trusted numerical premise.
theorem cover8_leaf1641_exp_radius : (997911729375861411/1000000000000000000 : ℝ) ≤ Real.exp ((-137/8192 : ℝ)/8) ∧ Real.exp ((-137/8192 : ℝ)/8) ≤ (249477932343965353/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-137/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1641_exp_lower : (920117797450468967/1000000000000000000 : ℝ) ≤ Real.exp ((-2664114445713/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664114445713/4000000000000 : ℝ)/8) ≤ (115014724681308621/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664114445713/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1641_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054979248187/1000000000000 : ℝ) ≤ 4*Real.exp (2191/16384 : ℝ)*Real.exp (-mu (radius 8 (137/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2054979248187/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (137/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1641_exp_radius
  have hrNumeric : (983415430839/1000000000000 : ℝ) ≤ Real.exp (-137/8192 : ℝ) ∧ Real.exp (-137/8192 : ℝ) ≤ (24585385771/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983415430839/1000000000000 : ℝ) ≤ (radius 8 (137/1024 : ℝ)) ∧ (radius 8 (137/1024 : ℝ)) ≤ (24585385771/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (137/1024 : ℝ)) (983415430839/1000000000000 : ℝ) (24585385771/25000000000 : ℝ) (181367280361/1000000000000 : ℝ) (11335455023/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (137/1024 : ℝ)) (983415430839/1000000000000 : ℝ) (24585385771/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (137/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983415430839/1000000000000 : ℝ) (24585385771/25000000000 : ℝ) (991707715419/1000000000000 : ℝ) (49585385771/50000000000 : ℝ) (49583652317/50000000000 : ℝ) (495836523171/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (137/1024 : ℝ)) 1 (991707715419/1000000000000 : ℝ) (49585385771/50000000000 : ℝ) (49583652317/50000000000 : ℝ) (495836523171/500000000000 : ℝ) (991690380879/1000000000000 : ℝ) (991690380881/1000000000000 : ℝ) (991690380727/1000000000000 : ℝ) (99169038073/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (137/1024 : ℝ)) 2 (991690380879/1000000000000 : ℝ) (991690380881/1000000000000 : ℝ) (991690380727/1000000000000 : ℝ) (99169038073/100000000000 : ℝ) (991690380803/1000000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (137/1024 : ℝ)) 3 (991690380803/1000000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (137/1024 : ℝ)) 4 (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (137/1024 : ℝ)) 5 (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (137/1024 : ℝ)) 6 (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (137/1024 : ℝ)) 7 (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (137/1024 : ℝ))) (181367280361/1000000000000 : ℝ) (11335455023/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181367280361/1000000000000 : ℝ) (11335455023/62500000000 : ℝ) (29534182009/50000000000 : ℝ) (73835455023/125000000000 : ℝ) (53234046959/125000000000 : ℝ) (425872375681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 1 (29534182009/50000000000 : ℝ) (73835455023/125000000000 : ℝ) (53234046959/125000000000 : ℝ) (425872375681/1000000000000 : ℝ) (254139003963/500000000000 : ℝ) (508278007933/1000000000000 : ℝ) (501553431963/1000000000000 : ℝ) (501553431971/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 2 (254139003963/500000000000 : ℝ) (508278007933/1000000000000 : ℝ) (501553431963/1000000000000 : ℝ) (501553431971/1000000000000 : ℝ) (63114464993/125000000000 : ℝ) (31557232497/62500000000 : ℝ) (252452262451/500000000000 : ℝ) (50490452491/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 3 (63114464993/125000000000 : ℝ) (31557232497/62500000000 : ℝ) (252452262451/500000000000 : ℝ) (50490452491/100000000000 : ℝ) (504910122423/1000000000000 : ℝ) (504910122431/1000000000000 : ℝ) (504910122391/1000000000000 : ℝ) (631137653/1250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 4 (504910122423/1000000000000 : ℝ) (504910122431/1000000000000 : ℝ) (504910122391/1000000000000 : ℝ) (631137653/1250000000 : ℝ) (504910122407/1000000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 5 (504910122407/1000000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 6 (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (137/1024 : ℝ))) 7 (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (137/1024 : ℝ)) hmem 8 (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (137/1024 : ℝ))) hcmem 8 (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (137/1024 : ℝ)) (495845190401/500000000000 : ℝ) (495845190403/500000000000 : ℝ) (252455061203/500000000000 : ℝ) (31556882651/62500000000 : ℝ) (24992394961/31250000000 : ℝ) (199939159693/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1641_exp_lower
  have heNumeric : (2054979248187/1000000000000 : ℝ)/4 ≤ Real.exp (-2664114445713/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054979248187/1000000000000 : ℝ)/4 ≤ Real.exp ((2191/16384 : ℝ)-(199939159693/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2191/16384 : ℝ) (137/1024 : ℝ) (199939159693/250000000000 : ℝ) (2054979248187/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1642; no trusted numerical premise.
theorem cover8_leaf1642_exp_radius : (498955388846764431/500000000000000000 : ℝ) ≤ Real.exp ((-2193/131072 : ℝ)/8) ∧ Real.exp ((-2193/131072 : ℝ)/8) ≤ (997910777693528863/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2193/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1642_exp_lower : (920118017737421169/1000000000000000000 : ℝ) ≤ Real.exp ((-133205339227/200000000000 : ℝ)/8) ∧ Real.exp ((-133205339227/200000000000 : ℝ)/8) ≤ (92011801773742117/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133205339227/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1642_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054983184079/1000000000000 : ℝ) ≤ 4*Real.exp (137/1024 : ℝ)*Real.exp (-mu (radius 8 (2193/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054983184079/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2193/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1642_exp_radius
  have hrNumeric : (983407928003/1000000000000 : ℝ) ≤ Real.exp (-2193/131072 : ℝ) ∧ Real.exp (-2193/131072 : ℝ) ≤ (245851982001/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983407928003/1000000000000 : ℝ) ≤ (radius 8 (2193/16384 : ℝ)) ∧ (radius 8 (2193/16384 : ℝ)) ≤ (245851982001/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2193/16384 : ℝ)) (983407928003/1000000000000 : ℝ) (245851982001/250000000000 : ℝ) (141724967/781250000 : ℝ) (181407957767/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2193/16384 : ℝ)) (983407928003/1000000000000 : ℝ) (245851982001/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983407928003/1000000000000 : ℝ) (245851982001/250000000000 : ℝ) (991703964001/1000000000000 : ℝ) (495851982001/500000000000 : ℝ) (198333852683/200000000000 : ℝ) (123958657927/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 1 (991703964001/1000000000000 : ℝ) (495851982001/500000000000 : ℝ) (198333852683/200000000000 : ℝ) (123958657927/125000000000 : ℝ) (247921653427/250000000000 : ℝ) (991686613709/1000000000000 : ℝ) (247921653389/250000000000 : ℝ) (495843306779/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 2 (247921653427/250000000000 : ℝ) (991686613709/1000000000000 : ℝ) (247921653389/250000000000 : ℝ) (495843306779/500000000000 : ℝ) (7747551669/7812500000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 3 (7747551669/7812500000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 4 (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 5 (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 6 (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2193/16384 : ℝ)) 7 (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2193/16384 : ℝ))) (141724967/781250000 : ℝ) (181407957767/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (141724967/781250000 : ℝ) (181407957767/1000000000000 : ℝ) (922974967/1562500000 : ℝ) (147675994721/250000000000 : ℝ) (53240016341/125000000000 : ℝ) (425920130737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 1 (922974967/1562500000 : ℝ) (147675994721/250000000000 : ℝ) (53240016341/125000000000 : ℝ) (425920130737/1000000000000 : ℝ) (127078013701/250000000000 : ℝ) (508312054811/1000000000000 : ℝ) (50159018721/100000000000 : ℝ) (250795093609/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 2 (127078013701/250000000000 : ℝ) (508312054811/1000000000000 : ℝ) (50159018721/100000000000 : ℝ) (250795093609/500000000000 : ℝ) (504951121007/1000000000000 : ℝ) (100990224203/200000000000 : ℝ) (126234983941/250000000000 : ℝ) (504939935773/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 3 (504951121007/1000000000000 : ℝ) (100990224203/200000000000 : ℝ) (126234983941/250000000000 : ℝ) (504939935773/1000000000000 : ℝ) (100989105677/200000000000 : ℝ) (252472764197/500000000000 : ℝ) (252472764177/500000000000 : ℝ) (126236382091/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 4 (100989105677/200000000000 : ℝ) (252472764197/500000000000 : ℝ) (252472764177/500000000000 : ℝ) (126236382091/250000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 5 (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 6 (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2193/16384 : ℝ))) 7 (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2193/16384 : ℝ)) hmem 8 (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2193/16384 : ℝ))) hcmem 8 (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2193/16384 : ℝ)) (991686613631/1000000000000 : ℝ) (495843306817/500000000000 : ℝ) (504945528369/1000000000000 : ℝ) (504945528379/1000000000000 : ℝ) (99976969827/125000000000 : ℝ) (159963151727/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1642_exp_lower
  have heNumeric : (2054983184079/1000000000000 : ℝ)/4 ≤ Real.exp (-133205339227/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054983184079/1000000000000 : ℝ)/4 ≤ Real.exp ((137/1024 : ℝ)-(159963151727/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (137/1024 : ℝ) (2193/16384 : ℝ) (159963151727/200000000000 : ℝ) (2054983184079/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1643; no trusted numerical premise.
theorem cover8_leaf1643_exp_radius : (249477456503025977/250000000000000000 : ℝ) ≤ Real.exp ((-1097/65536 : ℝ)/8) ∧ Real.exp ((-1097/65536 : ℝ)/8) ≤ (997909826012103909/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1097/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1643_exp_lower : (920118240119535341/1000000000000000000 : ℝ) ≤ Real.exp ((-2664099050503/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664099050503/4000000000000 : ℝ)/8) ≤ (460059120059767671/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664099050503/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1643_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513746789353/250000000000 : ℝ) ≤ 4*Real.exp (2193/16384 : ℝ)*Real.exp (-mu (radius 8 (1097/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (513746789353/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1097/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1643_exp_radius
  have hrNumeric : (122925053153/125000000000 : ℝ) ≤ Real.exp (-1097/65536 : ℝ) ∧ Real.exp (-1097/65536 : ℝ) ≤ (39336017009/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122925053153/125000000000 : ℝ) ≤ (radius 8 (1097/8192 : ℝ)) ∧ (radius 8 (1097/8192 : ℝ)) ≤ (39336017009/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1097/8192 : ℝ)) (122925053153/125000000000 : ℝ) (39336017009/40000000000 : ℝ) (181448625421/1000000000000 : ℝ) (181448625427/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1097/8192 : ℝ)) (122925053153/125000000000 : ℝ) (39336017009/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122925053153/125000000000 : ℝ) (39336017009/40000000000 : ℝ) (247925053153/250000000000 : ℝ) (991700212613/1000000000000 : ℝ) (123958185063/125000000000 : ℝ) (198333096101/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 1 (247925053153/250000000000 : ℝ) (991700212613/1000000000000 : ℝ) (123958185063/125000000000 : ℝ) (198333096101/200000000000 : ℝ) (495841423279/500000000000 : ℝ) (991682846559/1000000000000 : ℝ) (198336569281/200000000000 : ℝ) (991682846407/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 2 (495841423279/500000000000 : ℝ) (991682846559/1000000000000 : ℝ) (198336569281/200000000000 : ℝ) (991682846407/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 3 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 4 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 5 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 6 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1097/8192 : ℝ)) 7 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1097/8192 : ℝ))) (181448625421/1000000000000 : ℝ) (181448625427/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181448625421/1000000000000 : ℝ) (181448625427/1000000000000 : ℝ) (59072431271/100000000000 : ℝ) (295362156357/500000000000 : ℝ) (425967869/1000000000 : ℝ) (26622991813/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 1 (59072431271/100000000000 : ℝ) (295362156357/500000000000 : ℝ) (425967869/1000000000 : ℝ) (26622991813/62500000000 : ℝ) (101669218171/200000000000 : ℝ) (508346090861/1000000000000 : ℝ) (501626929751/1000000000000 : ℝ) (250813464879/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 2 (101669218171/200000000000 : ℝ) (508346090861/1000000000000 : ℝ) (501626929751/1000000000000 : ℝ) (250813464879/500000000000 : ℝ) (504986510303/1000000000000 : ℝ) (50498651031/100000000000 : ℝ) (504975334849/1000000000000 : ℝ) (504975334857/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 3 (504986510303/1000000000000 : ℝ) (50498651031/100000000000 : ℝ) (504975334849/1000000000000 : ℝ) (504975334857/1000000000000 : ℝ) (31561307661/62500000000 : ℝ) (63122615323/125000000000 : ℝ) (100996184509/200000000000 : ℝ) (504980922553/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 4 (31561307661/62500000000 : ℝ) (63122615323/125000000000 : ℝ) (100996184509/200000000000 : ℝ) (504980922553/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 5 (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 6 (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1097/8192 : ℝ))) 7 (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1097/8192 : ℝ)) hmem 8 (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1097/8192 : ℝ))) hcmem 8 (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1097/8192 : ℝ)) (991682846481/1000000000000 : ℝ) (991682846483/1000000000000 : ℝ) (1578065383/3125000000 : ℝ) (504980922569/1000000000000 : ℝ) (159974972053/200000000000 : ℝ) (399937430141/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1643_exp_lower
  have heNumeric : (513746789353/250000000000 : ℝ)/4 ≤ Real.exp (-2664099050503/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513746789353/250000000000 : ℝ)/4 ≤ Real.exp ((2193/16384 : ℝ)-(399937430141/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2193/16384 : ℝ) (1097/8192 : ℝ) (399937430141/500000000000 : ℝ) (513746789353/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1644; no trusted numerical premise.
theorem cover8_leaf1644_exp_radius : (249477218582896637/250000000000000000 : ℝ) ≤ Real.exp ((-2195/131072 : ℝ)/8) ∧ Real.exp ((-2195/131072 : ℝ)/8) ≤ (997908874331586549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2195/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1644_exp_lower : (230029616148973221/250000000000000000 : ℝ) ≤ Real.exp ((-1332045621817/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332045621817/2000000000000 : ℝ)/8) ≤ (184023692919178577/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332045621817/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1644_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054991168169/1000000000000 : ℝ) ≤ 4*Real.exp (1097/8192 : ℝ)*Real.exp (-mu (radius 8 (2195/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054991168169/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2195/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1644_exp_radius
  have hrNumeric : (983392922503/1000000000000 : ℝ) ≤ Real.exp (-2195/131072 : ℝ) ∧ Real.exp (-2195/131072 : ℝ) ≤ (122924115313/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983392922503/1000000000000 : ℝ) ≤ (radius 8 (2195/16384 : ℝ)) ∧ (radius 8 (2195/16384 : ℝ)) ≤ (122924115313/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2195/16384 : ℝ)) (983392922503/1000000000000 : ℝ) (122924115313/125000000000 : ℝ) (11343080209/62500000000 : ℝ) (181489283351/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2195/16384 : ℝ)) (983392922503/1000000000000 : ℝ) (122924115313/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983392922503/1000000000000 : ℝ) (122924115313/125000000000 : ℝ) (991696461251/1000000000000 : ℝ) (247924115313/250000000000 : ℝ) (123957712201/125000000000 : ℝ) (991661697609/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 1 (991696461251/1000000000000 : ℝ) (247924115313/250000000000 : ℝ) (123957712201/125000000000 : ℝ) (991661697609/1000000000000 : ℝ) (991679079429/1000000000000 : ℝ) (991679079431/1000000000000 : ℝ) (991679079277/1000000000000 : ℝ) (991679079279/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 2 (991679079429/1000000000000 : ℝ) (991679079431/1000000000000 : ℝ) (991679079277/1000000000000 : ℝ) (991679079279/1000000000000 : ℝ) (991679079353/1000000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 3 (991679079353/1000000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 4 (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 5 (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 6 (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2195/16384 : ℝ)) 7 (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2195/16384 : ℝ))) (11343080209/62500000000 : ℝ) (181489283351/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11343080209/62500000000 : ℝ) (181489283351/1000000000000 : ℝ) (73843080209/125000000000 : ℝ) (147686160419/250000000000 : ℝ) (213007795247/500000000000 : ℝ) (426015590503/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 1 (73843080209/125000000000 : ℝ) (147686160419/250000000000 : ℝ) (213007795247/500000000000 : ℝ) (426015590503/1000000000000 : ℝ) (508380116083/1000000000000 : ℝ) (50838011609/100000000000 : ℝ) (501663659589/1000000000000 : ℝ) (501663659597/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 2 (508380116083/1000000000000 : ℝ) (50838011609/100000000000 : ℝ) (501663659589/1000000000000 : ℝ) (501663659597/1000000000000 : ℝ) (126255471959/250000000000 : ℝ) (126255471961/250000000000 : ℝ) (505010722159/1000000000000 : ℝ) (63126340271/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 3 (126255471959/250000000000 : ℝ) (126255471961/250000000000 : ℝ) (505010722159/1000000000000 : ℝ) (63126340271/125000000000 : ℝ) (505016304997/1000000000000 : ℝ) (252508152503/500000000000 : ℝ) (252508152483/500000000000 : ℝ) (31563519061/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 4 (505016304997/1000000000000 : ℝ) (252508152503/500000000000 : ℝ) (252508152483/500000000000 : ℝ) (31563519061/62500000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 5 (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 6 (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2195/16384 : ℝ))) 7 (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2195/16384 : ℝ)) hmem 8 (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2195/16384 : ℝ))) hcmem 8 (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2195/16384 : ℝ)) (123959884919/125000000000 : ℝ) (198335815871/200000000000 : ℝ) (505016304981/1000000000000 : ℝ) (505016304991/1000000000000 : ℝ) (399966971851/500000000000 : ℝ) (799933943721/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1644_exp_lower
  have heNumeric : (2054991168169/1000000000000 : ℝ)/4 ≤ Real.exp (-1332045621817/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054991168169/1000000000000 : ℝ)/4 ≤ Real.exp ((1097/8192 : ℝ)-(799933943721/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1097/8192 : ℝ) (2195/16384 : ℝ) (799933943721/1000000000000 : ℝ) (2054991168169/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1645; no trusted numerical premise.
theorem cover8_leaf1645_exp_radius : (49895396132598839/50000000000000000 : ℝ) ≤ Real.exp ((-549/32768 : ℝ)/8) ∧ Real.exp ((-549/32768 : ℝ)/8) ≤ (997907922651976781/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-549/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1645_exp_lower : (115014836395524379/125000000000000000 : ℝ) ≤ Real.exp ((-2664083364013/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664083364013/4000000000000 : ℝ)/8) ≤ (920118691164195033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664083364013/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1645_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054995216311/1000000000000 : ℝ) ≤ 4*Real.exp (2195/16384 : ℝ)*Real.exp (-mu (radius 8 (549/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054995216311/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (549/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1645_exp_radius
  have hrNumeric : (983385419839/1000000000000 : ℝ) ≤ Real.exp (-549/32768 : ℝ) ∧ Real.exp (-549/32768 : ℝ) ≤ (3073079437/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983385419839/1000000000000 : ℝ) ≤ (radius 8 (549/4096 : ℝ)) ∧ (radius 8 (549/4096 : ℝ)) ≤ (3073079437/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (549/4096 : ℝ)) (983385419839/1000000000000 : ℝ) (3073079437/3125000000 : ℝ) (181529931543/1000000000000 : ℝ) (181529931549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (549/4096 : ℝ)) (983385419839/1000000000000 : ℝ) (3073079437/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (549/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983385419839/1000000000000 : ℝ) (3073079437/3125000000 : ℝ) (991692709919/1000000000000 : ℝ) (6198079437/6250000000 : ℝ) (495828957363/500000000000 : ℝ) (991657914727/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (549/4096 : ℝ)) 1 (991692709919/1000000000000 : ℝ) (6198079437/6250000000 : ℝ) (495828957363/500000000000 : ℝ) (991657914727/1000000000000 : ℝ) (495837656161/500000000000 : ℝ) (247918828081/250000000000 : ℝ) (991675312169/1000000000000 : ℝ) (991675312171/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (549/4096 : ℝ)) 2 (495837656161/500000000000 : ℝ) (247918828081/250000000000 : ℝ) (991675312169/1000000000000 : ℝ) (991675312171/1000000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (549/4096 : ℝ)) 3 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (549/4096 : ℝ)) 4 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (549/4096 : ℝ)) 5 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (549/4096 : ℝ)) 6 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (549/4096 : ℝ)) 7 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (549/4096 : ℝ))) (181529931543/1000000000000 : ℝ) (181529931549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181529931543/1000000000000 : ℝ) (181529931549/1000000000000 : ℝ) (590764965771/1000000000000 : ℝ) (23630598631/40000000000 : ℝ) (42606329523/100000000000 : ℝ) (213031647619/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 1 (590764965771/1000000000000 : ℝ) (23630598631/40000000000 : ℝ) (42606329523/100000000000 : ℝ) (213031647619/500000000000 : ℝ) (1016828261/2000000000 : ℝ) (508414130507/1000000000000 : ℝ) (501700376741/1000000000000 : ℝ) (501700376749/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 2 (1016828261/2000000000 : ℝ) (508414130507/1000000000000 : ℝ) (501700376741/1000000000000 : ℝ) (501700376749/1000000000000 : ℝ) (25252862681/50000000000 : ℝ) (126264313407/250000000000 : ℝ) (50504609771/100000000000 : ℝ) (252523048859/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 3 (25252862681/50000000000 : ℝ) (126264313407/250000000000 : ℝ) (50504609771/100000000000 : ℝ) (252523048859/500000000000 : ℝ) (101010335133/200000000000 : ℝ) (505051675673/1000000000000 : ℝ) (252525837817/500000000000 : ℝ) (505051675643/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 4 (101010335133/200000000000 : ℝ) (505051675673/1000000000000 : ℝ) (252525837817/500000000000 : ℝ) (505051675643/1000000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 5 (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 6 (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (549/4096 : ℝ))) 7 (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (549/4096 : ℝ)) hmem 8 (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (549/4096 : ℝ))) hcmem 8 (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (549/4096 : ℝ)) (198335062449/200000000000 : ℝ) (123959414031/125000000000 : ℝ) (505051675649/1000000000000 : ℝ) (252525837829/500000000000 : ℝ) (399996504477/500000000000 : ℝ) (199998252243/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1645_exp_lower
  have heNumeric : (2054995216311/1000000000000 : ℝ)/4 ≤ Real.exp (-2664083364013/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054995216311/1000000000000 : ℝ)/4 ≤ Real.exp ((2195/16384 : ℝ)-(199998252243/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2195/16384 : ℝ) (549/4096 : ℝ) (199998252243/250000000000 : ℝ) (2054995216311/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1646; no trusted numerical premise.
theorem cover8_leaf1646_exp_radius : (249476742743318651/250000000000000000 : ℝ) ≤ Real.exp ((-2197/131072 : ℝ)/8) ∧ Real.exp ((-2197/131072 : ℝ)/8) ≤ (199581394194654921/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2197/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1646_exp_lower : (460059459911704099/500000000000000000 : ℝ) ≤ Real.exp ((-666018852919/1000000000000 : ℝ)/8) ∧ Real.exp ((-666018852919/1000000000000 : ℝ)/8) ≤ (920118919823408199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666018852919/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1646_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054999301819/1000000000000 : ℝ) ≤ 4*Real.exp (549/4096 : ℝ)*Real.exp (-mu (radius 8 (2197/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054999301819/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2197/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1646_exp_radius
  have hrNumeric : (983377917233/1000000000000 : ℝ) ≤ Real.exp (-2197/131072 : ℝ) ∧ Real.exp (-2197/131072 : ℝ) ≤ (491688958617/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983377917233/1000000000000 : ℝ) ≤ (radius 8 (2197/16384 : ℝ)) ∧ (radius 8 (2197/16384 : ℝ)) ≤ (491688958617/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2197/16384 : ℝ)) (983377917233/1000000000000 : ℝ) (491688958617/500000000000 : ℝ) (181570570017/1000000000000 : ℝ) (22696321253/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2197/16384 : ℝ)) (983377917233/1000000000000 : ℝ) (491688958617/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983377917233/1000000000000 : ℝ) (491688958617/500000000000 : ℝ) (123961119827/125000000000 : ℝ) (991688958617/1000000000000 : ℝ) (495827065929/500000000000 : ℝ) (49582706593/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 1 (123961119827/125000000000 : ℝ) (991688958617/1000000000000 : ℝ) (495827065929/500000000000 : ℝ) (49582706593/50000000000 : ℝ) (991671545237/1000000000000 : ℝ) (991671545239/1000000000000 : ℝ) (247917886271/250000000000 : ℝ) (495835772543/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 2 (991671545237/1000000000000 : ℝ) (991671545239/1000000000000 : ℝ) (247917886271/250000000000 : ℝ) (495835772543/500000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 3 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 4 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 5 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 6 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2197/16384 : ℝ)) 7 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2197/16384 : ℝ))) (181570570017/1000000000000 : ℝ) (22696321253/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181570570017/1000000000000 : ℝ) (22696321253/125000000000 : ℝ) (36924080313/62500000000 : ℝ) (147696321253/250000000000 : ℝ) (85222196643/200000000000 : ℝ) (53263872903/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 1 (36924080313/62500000000 : ℝ) (147696321253/250000000000 : ℝ) (85222196643/200000000000 : ℝ) (53263872903/125000000000 : ℝ) (508448134111/1000000000000 : ℝ) (254224067059/500000000000 : ℝ) (125434270303/250000000000 : ℝ) (25086854061/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 2 (508448134111/1000000000000 : ℝ) (254224067059/500000000000 : ℝ) (125434270303/250000000000 : ℝ) (25086854061/50000000000 : ℝ) (505092607661/1000000000000 : ℝ) (505092607669/1000000000000 : ℝ) (101016292301/200000000000 : ℝ) (252540730757/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 3 (505092607661/1000000000000 : ℝ) (505092607669/1000000000000 : ℝ) (101016292301/200000000000 : ℝ) (252540730757/500000000000 : ℝ) (505087034583/1000000000000 : ℝ) (15783969831/31250000000 : ℝ) (63135879319/125000000000 : ℝ) (505087034561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 4 (505087034583/1000000000000 : ℝ) (15783969831/31250000000 : ℝ) (63135879319/125000000000 : ℝ) (505087034561/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 5 (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 6 (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2197/16384 : ℝ))) 7 (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2197/16384 : ℝ)) hmem 8 (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2197/16384 : ℝ))) hcmem 8 (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2197/16384 : ℝ)) (24791788629/25000000000 : ℝ) (991671545163/1000000000000 : ℝ) (505087034567/1000000000000 : ℝ) (505087034577/1000000000000 : ℝ) (32002082241/40000000000 : ℝ) (200013014011/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1646_exp_lower
  have heNumeric : (2054999301819/1000000000000 : ℝ)/4 ≤ Real.exp (-666018852919/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054999301819/1000000000000 : ℝ)/4 ≤ Real.exp ((549/4096 : ℝ)-(200013014011/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (549/4096 : ℝ) (2197/16384 : ℝ) (200013014011/250000000000 : ℝ) (2054999301819/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1647; no trusted numerical premise.
theorem cover8_leaf1647_exp_radius : (49895300964774001/50000000000000000 : ℝ) ≤ Real.exp ((-1099/65536 : ℝ)/8) ∧ Real.exp ((-1099/65536 : ℝ)/8) ≤ (997906019295480021/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1099/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1647_exp_lower : (92011915057019851/100000000000000000 : ℝ) ≤ Real.exp ((-2664067386739/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664067386739/4000000000000 : ℝ)/8) ≤ (920119150570198511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664067386739/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1647_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055003424633/1000000000000 : ℝ) ≤ 4*Real.exp (2197/16384 : ℝ)*Real.exp (-mu (radius 8 (1099/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055003424633/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1099/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1647_exp_radius
  have hrNumeric : (983370414683/1000000000000 : ℝ) ≤ Real.exp (-1099/65536 : ℝ) ∧ Real.exp (-1099/65536 : ℝ) ≤ (245842603671/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983370414683/1000000000000 : ℝ) ≤ (radius 8 (1099/8192 : ℝ)) ∧ (radius 8 (1099/8192 : ℝ)) ≤ (245842603671/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1099/8192 : ℝ)) (983370414683/1000000000000 : ℝ) (245842603671/250000000000 : ℝ) (36322239757/200000000000 : ℝ) (181611198791/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1099/8192 : ℝ)) (983370414683/1000000000000 : ℝ) (245842603671/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983370414683/1000000000000 : ℝ) (245842603671/250000000000 : ℝ) (991685207341/1000000000000 : ℝ) (495842603671/500000000000 : ℝ) (198330069801/200000000000 : ℝ) (991650349007/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 1 (991685207341/1000000000000 : ℝ) (495842603671/500000000000 : ℝ) (198330069801/200000000000 : ℝ) (991650349007/1000000000000 : ℝ) (991667778173/1000000000000 : ℝ) (39666711127/40000000000 : ℝ) (991667778019/1000000000000 : ℝ) (495833889011/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 2 (991667778173/1000000000000 : ℝ) (39666711127/40000000000 : ℝ) (991667778019/1000000000000 : ℝ) (495833889011/500000000000 : ℝ) (61979236131/62500000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 3 (61979236131/62500000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 4 (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 5 (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 6 (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1099/8192 : ℝ)) 7 (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1099/8192 : ℝ))) (36322239757/200000000000 : ℝ) (181611198791/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36322239757/200000000000 : ℝ) (181611198791/1000000000000 : ℝ) (18462674981/31250000000 : ℝ) (147701399849/250000000000 : ℝ) (106539663619/250000000000 : ℝ) (106539663621/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 1 (18462674981/31250000000 : ℝ) (147701399849/250000000000 : ℝ) (106539663619/250000000000 : ℝ) (106539663621/250000000000 : ℝ) (254241063467/500000000000 : ℝ) (25424106347/50000000000 : ℝ) (501773773023/1000000000000 : ℝ) (50177377303/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 2 (254241063467/500000000000 : ℝ) (25424106347/50000000000 : ℝ) (501773773023/1000000000000 : ℝ) (50177377303/100000000000 : ℝ) (252563974989/500000000000 : ℝ) (101025589997/200000000000 : ℝ) (101023362713/200000000000 : ℝ) (126279203393/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 3 (252563974989/500000000000 : ℝ) (101025589997/200000000000 : ℝ) (101023362713/200000000000 : ℝ) (126279203393/250000000000 : ℝ) (505122381771/1000000000000 : ℝ) (505122381779/1000000000000 : ℝ) (25256119087/50000000000 : ℝ) (126280595437/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 4 (505122381771/1000000000000 : ℝ) (505122381779/1000000000000 : ℝ) (25256119087/50000000000 : ℝ) (126280595437/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 5 (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 6 (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1099/8192 : ℝ))) 7 (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1099/8192 : ℝ)) hmem 8 (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1099/8192 : ℝ))) hcmem 8 (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1099/8192 : ℝ)) (198333555619/200000000000 : ℝ) (991667778099/1000000000000 : ℝ) (101024476351/200000000000 : ℝ) (126280595441/250000000000 : ℝ) (800111084947/1000000000000 : ℝ) (400055542483/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1647_exp_lower
  have heNumeric : (2055003424633/1000000000000 : ℝ)/4 ≤ Real.exp (-2664067386739/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055003424633/1000000000000 : ℝ)/4 ≤ Real.exp ((2197/16384 : ℝ)-(400055542483/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2197/16384 : ℝ) (1099/8192 : ℝ) (400055542483/500000000000 : ℝ) (2055003424633/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1648; no trusted numerical premise.
theorem cover8_leaf1648_exp_radius : (39916202704743721/40000000000000000 : ℝ) ≤ Real.exp ((-2199/131072 : ℝ)/8) ∧ Real.exp ((-2199/131072 : ℝ)/8) ≤ (498952533809296513/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2199/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1648_exp_lower : (460059691702398783/500000000000000000 : ℝ) ≤ Real.exp ((-1332029644597/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332029644597/2000000000000 : ℝ)/8) ≤ (920119383404797567/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332029644597/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1648_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027503792379/500000000000 : ℝ) ≤ 4*Real.exp (1099/8192 : ℝ)*Real.exp (-mu (radius 8 (2199/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027503792379/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2199/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1648_exp_radius
  have hrNumeric : (983362912191/1000000000000 : ℝ) ≤ Real.exp (-2199/131072 : ℝ) ∧ Real.exp (-2199/131072 : ℝ) ≤ (15365045503/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983362912191/1000000000000 : ℝ) ≤ (radius 8 (2199/16384 : ℝ)) ∧ (radius 8 (2199/16384 : ℝ)) ≤ (15365045503/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2199/16384 : ℝ)) (983362912191/1000000000000 : ℝ) (15365045503/15625000000 : ℝ) (181651817841/1000000000000 : ℝ) (22706477231/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2199/16384 : ℝ)) (983362912191/1000000000000 : ℝ) (15365045503/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983362912191/1000000000000 : ℝ) (15365045503/15625000000 : ℝ) (198336291219/200000000000 : ℝ) (30990045503/31250000000 : ℝ) (991646566167/1000000000000 : ℝ) (123955820771/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 1 (198336291219/200000000000 : ℝ) (30990045503/31250000000 : ℝ) (991646566167/1000000000000 : ℝ) (123955820771/125000000000 : ℝ) (991664011131/1000000000000 : ℝ) (247916002783/250000000000 : ℝ) (991664010977/1000000000000 : ℝ) (991664010979/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 2 (991664011131/1000000000000 : ℝ) (247916002783/250000000000 : ℝ) (991664010977/1000000000000 : ℝ) (991664010979/1000000000000 : ℝ) (495832005527/500000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 3 (495832005527/500000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 4 (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 5 (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 6 (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2199/16384 : ℝ)) 7 (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2199/16384 : ℝ))) (181651817841/1000000000000 : ℝ) (22706477231/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181651817841/1000000000000 : ℝ) (22706477231/125000000000 : ℝ) (14770647723/25000000000 : ℝ) (147706477231/250000000000 : ℝ) (426206309011/1000000000000 : ℝ) (21310315451/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 1 (14770647723/25000000000 : ℝ) (147706477231/250000000000 : ℝ) (426206309011/1000000000000 : ℝ) (21310315451/50000000000 : ℝ) (101703221793/200000000000 : ℝ) (127129027243/250000000000 : ℝ) (501810452171/1000000000000 : ℝ) (501810452179/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 2 (101703221793/200000000000 : ℝ) (127129027243/250000000000 : ℝ) (501810452171/1000000000000 : ℝ) (501810452179/1000000000000 : ℝ) (63145410071/125000000000 : ℝ) (7893176259/15625000000 : ℝ) (252576076943/500000000000 : ℝ) (252576076947/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 3 (63145410071/125000000000 : ℝ) (7893176259/15625000000 : ℝ) (252576076943/500000000000 : ℝ) (252576076947/500000000000 : ℝ) (505157717227/1000000000000 : ℝ) (101031543447/200000000000 : ℝ) (126289429299/250000000000 : ℝ) (101031543441/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 4 (505157717227/1000000000000 : ℝ) (101031543447/200000000000 : ℝ) (126289429299/250000000000 : ℝ) (101031543441/200000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 5 (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 6 (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2199/16384 : ℝ))) 7 (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2199/16384 : ℝ)) hmem 8 (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2199/16384 : ℝ))) hcmem 8 (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2199/16384 : ℝ)) (991664011053/1000000000000 : ℝ) (61979000691/62500000000 : ℝ) (505157717211/1000000000000 : ℝ) (25257885861/50000000000 : ℝ) (400085047859/500000000000 : ℝ) (100021261967/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1648_exp_lower
  have heNumeric : (1027503792379/500000000000 : ℝ)/4 ≤ Real.exp (-1332029644597/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027503792379/500000000000 : ℝ)/4 ≤ Real.exp ((1099/8192 : ℝ)-(100021261967/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1099/8192 : ℝ) (2199/16384 : ℝ) (100021261967/125000000000 : ℝ) (1027503792379/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1649; no trusted numerical premise.
theorem cover8_leaf1649_exp_radius : (49895205797130681/50000000000000000 : ℝ) ≤ Real.exp ((-275/16384 : ℝ)/8) ∧ Real.exp ((-275/16384 : ℝ)/8) ≤ (997904115942613621/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-275/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1649_exp_lower : (920119618324446593/1000000000000000000 : ℝ) ≤ Real.exp ((-2664051119137/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664051119137/4000000000000 : ℝ)/8) ≤ (460059809162223297/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664051119137/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1649_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (4013694887/1953125000 : ℝ) ≤ 4*Real.exp (2199/16384 : ℝ)*Real.exp (-mu (radius 8 (275/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (4013694887/1953125000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (275/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1649_exp_radius
  have hrNumeric : (245838852439/250000000000 : ℝ) ≤ Real.exp (-275/16384 : ℝ) ∧ Real.exp (-275/16384 : ℝ) ≤ (983355409757/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245838852439/250000000000 : ℝ) ≤ (radius 8 (275/2048 : ℝ)) ∧ (radius 8 (275/2048 : ℝ)) ≤ (983355409757/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (275/2048 : ℝ)) (245838852439/250000000000 : ℝ) (983355409757/1000000000000 : ℝ) (181692427199/1000000000000 : ℝ) (36338485441/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (275/2048 : ℝ)) (245838852439/250000000000 : ℝ) (983355409757/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (275/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245838852439/250000000000 : ℝ) (983355409757/1000000000000 : ℝ) (495838852439/500000000000 : ℝ) (991677704879/1000000000000 : ℝ) (495821391671/500000000000 : ℝ) (61977673959/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (275/2048 : ℝ)) 1 (495838852439/500000000000 : ℝ) (991677704879/1000000000000 : ℝ) (495821391671/500000000000 : ℝ) (61977673959/62500000000 : ℝ) (99166024411/100000000000 : ℝ) (61978765257/62500000000 : ℝ) (247915060989/250000000000 : ℝ) (495830121979/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (275/2048 : ℝ)) 2 (99166024411/100000000000 : ℝ) (61978765257/62500000000 : ℝ) (247915060989/250000000000 : ℝ) (495830121979/500000000000 : ℝ) (991660244033/1000000000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (275/2048 : ℝ)) 3 (991660244033/1000000000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (275/2048 : ℝ)) 4 (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (275/2048 : ℝ)) 5 (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (275/2048 : ℝ)) 6 (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (275/2048 : ℝ)) 7 (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (275/2048 : ℝ))) (181692427199/1000000000000 : ℝ) (36338485441/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181692427199/1000000000000 : ℝ) (36338485441/200000000000 : ℝ) (590846213599/1000000000000 : ℝ) (590846213603/1000000000000 : ℝ) (213126973421/500000000000 : ℝ) (8525078937/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 1 (590846213599/1000000000000 : ℝ) (590846213603/1000000000000 : ℝ) (213126973421/500000000000 : ℝ) (8525078937/20000000000 : ℝ) (25427504011/50000000000 : ℝ) (508550080227/1000000000000 : ℝ) (20073884747/40000000000 : ℝ) (501847118683/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 2 (25427504011/50000000000 : ℝ) (508550080227/1000000000000 : ℝ) (20073884747/40000000000 : ℝ) (501847118683/1000000000000 : ℝ) (505198599447/1000000000000 : ℝ) (101039719891/200000000000 : ℝ) (101037496497/200000000000 : ℝ) (252593741247/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 3 (505198599447/1000000000000 : ℝ) (101039719891/200000000000 : ℝ) (101037496497/200000000000 : ℝ) (252593741247/500000000000 : ℝ) (252596520483/500000000000 : ℝ) (20207721639/40000000000 : ℝ) (101038608187/200000000000 : ℝ) (31574565059/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 4 (252596520483/500000000000 : ℝ) (20207721639/40000000000 : ℝ) (101038608187/200000000000 : ℝ) (31574565059/62500000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 5 (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 6 (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (275/2048 : ℝ))) 7 (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (275/2048 : ℝ)) hmem 8 (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (275/2048 : ℝ))) hcmem 8 (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (275/2048 : ℝ)) (15494691313/15625000000 : ℝ) (198332048807/200000000000 : ℝ) (10103860819/20000000000 : ℝ) (1578728253/3125000000 : ℝ) (800229088359/1000000000000 : ℝ) (400114544189/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1649_exp_lower
  have heNumeric : (4013694887/1953125000 : ℝ)/4 ≤ Real.exp (-2664051119137/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (4013694887/1953125000 : ℝ)/4 ≤ Real.exp ((2199/16384 : ℝ)-(400114544189/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2199/16384 : ℝ) (275/2048 : ℝ) (400114544189/500000000000 : ℝ) (4013694887/1953125000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1625_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1625_certificate
#check SmaleRate.Proofs.cover8_leaf1626_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1626_certificate
#check SmaleRate.Proofs.cover8_leaf1627_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1627_certificate
#check SmaleRate.Proofs.cover8_leaf1628_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1628_certificate
#check SmaleRate.Proofs.cover8_leaf1629_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1629_certificate
#check SmaleRate.Proofs.cover8_leaf1630_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1630_certificate
#check SmaleRate.Proofs.cover8_leaf1631_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1631_certificate
#check SmaleRate.Proofs.cover8_leaf1632_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1632_certificate
#check SmaleRate.Proofs.cover8_leaf1633_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1633_certificate
#check SmaleRate.Proofs.cover8_leaf1634_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1634_certificate
#check SmaleRate.Proofs.cover8_leaf1635_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1635_certificate
#check SmaleRate.Proofs.cover8_leaf1636_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1636_certificate
#check SmaleRate.Proofs.cover8_leaf1637_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1637_certificate
#check SmaleRate.Proofs.cover8_leaf1638_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1638_certificate
#check SmaleRate.Proofs.cover8_leaf1639_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1639_certificate
#check SmaleRate.Proofs.cover8_leaf1640_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1640_certificate
#check SmaleRate.Proofs.cover8_leaf1641_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1641_certificate
#check SmaleRate.Proofs.cover8_leaf1642_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1642_certificate
#check SmaleRate.Proofs.cover8_leaf1643_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1643_certificate
#check SmaleRate.Proofs.cover8_leaf1644_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1644_certificate
#check SmaleRate.Proofs.cover8_leaf1645_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1645_certificate
#check SmaleRate.Proofs.cover8_leaf1646_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1646_certificate
#check SmaleRate.Proofs.cover8_leaf1647_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1647_certificate
#check SmaleRate.Proofs.cover8_leaf1648_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1648_certificate
#check SmaleRate.Proofs.cover8_leaf1649_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1649_certificate
