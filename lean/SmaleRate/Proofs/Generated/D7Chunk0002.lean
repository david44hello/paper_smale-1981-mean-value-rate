/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0050; no trusted numerical premise.
theorem cover7_leaf0050_exp_radius : (498869948725640767/500000000000000000 : ℝ) ≤ Real.exp ((-519/28672 : ℝ)/8) ∧ Real.exp ((-519/28672 : ℝ)/8) ≤ (199547979490256307/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-519/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0050_exp_lower : (918089280409938041/1000000000000000000 : ℝ) ≤ Real.exp ((-683685101937/1000000000000 : ℝ)/8) ∧ Real.exp ((-683685101937/1000000000000 : ℝ)/8) ≤ (459044640204969021/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683685101937/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0050_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013971229/1000000000000 : ℝ) ≤ 4*Real.exp (259/2048 : ℝ)*Real.exp (-mu (radius 7 (519/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013971229/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (519/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0050_exp_radius
  have hrNumeric : (491030780353/500000000000 : ℝ) ≤ Real.exp (-519/28672 : ℝ) ∧ Real.exp (-519/28672 : ℝ) ≤ (982061560707/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491030780353/500000000000 : ℝ) ≤ (radius 7 (519/4096 : ℝ)) ∧ (radius 7 (519/4096 : ℝ)) ≤ (982061560707/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (519/4096 : ℝ)) (491030780353/500000000000 : ℝ) (982061560707/1000000000000 : ℝ) (7542423057/40000000000 : ℝ) (188560576431/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (519/4096 : ℝ)) (491030780353/500000000000 : ℝ) (982061560707/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (519/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491030780353/500000000000 : ℝ) (982061560707/1000000000000 : ℝ) (991030780353/1000000000000 : ℝ) (495515390177/500000000000 : ℝ) (990990192033/1000000000000 : ℝ) (495495096017/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (519/4096 : ℝ)) 1 (991030780353/1000000000000 : ℝ) (495515390177/500000000000 : ℝ) (990990192033/1000000000000 : ℝ) (495495096017/500000000000 : ℝ) (991010486193/1000000000000 : ℝ) (495505243097/500000000000 : ℝ) (198202097197/200000000000 : ℝ) (991010485987/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (519/4096 : ℝ)) 2 (991010486193/1000000000000 : ℝ) (495505243097/500000000000 : ℝ) (198202097197/200000000000 : ℝ) (991010485987/1000000000000 : ℝ) (991010486089/1000000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (519/4096 : ℝ)) 3 (991010486089/1000000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (519/4096 : ℝ)) 4 (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (519/4096 : ℝ)) 5 (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (519/4096 : ℝ)) 6 (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (519/4096 : ℝ)) 7 (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (519/4096 : ℝ))) (7542423057/40000000000 : ℝ) (188560576431/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7542423057/40000000000 : ℝ) (188560576431/1000000000000 : ℝ) (148570072053/250000000000 : ℝ) (74285036027/125000000000 : ℝ) (108558905791/250000000000 : ℝ) (108558905793/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 1 (148570072053/250000000000 : ℝ) (74285036027/125000000000 : ℝ) (108558905791/250000000000 : ℝ) (108558905793/250000000000 : ℝ) (64282244461/125000000000 : ℝ) (257128977847/500000000000 : ℝ) (15874805341/31250000000 : ℝ) (507993770919/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 2 (64282244461/125000000000 : ℝ) (257128977847/500000000000 : ℝ) (15874805341/31250000000 : ℝ) (507993770919/1000000000000 : ℝ) (5111258633/10000000000 : ℝ) (511125863307/1000000000000 : ℝ) (102223253349/200000000000 : ℝ) (1996547917/3906250000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 3 (5111258633/10000000000 : ℝ) (511125863307/1000000000000 : ℝ) (102223253349/200000000000 : ℝ) (1996547917/3906250000 : ℝ) (255560532511/500000000000 : ℝ) (51112106503/100000000000 : ℝ) (511121064999/1000000000000 : ℝ) (511121065007/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 4 (255560532511/500000000000 : ℝ) (51112106503/100000000000 : ℝ) (511121064999/1000000000000 : ℝ) (511121065007/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 5 (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 6 (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (519/4096 : ℝ))) 7 (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (519/4096 : ℝ)) hmem 8 (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (519/4096 : ℝ))) hcmem 8 (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (519/4096 : ℝ)) (123876310761/125000000000 : ℝ) (991010486091/1000000000000 : ℝ) (51112106501/100000000000 : ℝ) (511121065019/1000000000000 : ℝ) (81014994567/100000000000 : ℝ) (810149945687/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0050_exp_lower
  have heNumeric : (2019013971229/1000000000000 : ℝ)/4 ≤ Real.exp (-683685101937/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013971229/1000000000000 : ℝ)/4 ≤ Real.exp ((259/2048 : ℝ)-(810149945687/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (259/2048 : ℝ) (519/4096 : ℝ) (810149945687/1000000000000 : ℝ) (2019013971229/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0051; no trusted numerical premise.
theorem cover7_leaf0051_exp_radius : (249434430638318909/250000000000000000 : ℝ) ≤ Real.exp ((-1039/57344 : ℝ)/8) ∧ Real.exp ((-1039/57344 : ℝ)/8) ≤ (997737722553275637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1039/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0051_exp_lower : (459051299270153719/500000000000000000 : ℝ) ≤ Real.exp ((-683569051927/1000000000000 : ℝ)/8) ∧ Real.exp ((-683569051927/1000000000000 : ℝ)/8) ≤ (918102598540307439/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683569051927/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0051_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019248291417/1000000000000 : ℝ) ≤ 4*Real.exp (519/4096 : ℝ)*Real.exp (-mu (radius 7 (1039/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019248291417/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1039/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0051_exp_radius
  have hrNumeric : (982044435061/1000000000000 : ℝ) ≤ Real.exp (-1039/57344 : ℝ) ∧ Real.exp (-1039/57344 : ℝ) ≤ (491022217531/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982044435061/1000000000000 : ℝ) ≤ (radius 7 (1039/8192 : ℝ)) ∧ (radius 7 (1039/8192 : ℝ)) ≤ (491022217531/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1039/8192 : ℝ)) (982044435061/1000000000000 : ℝ) (491022217531/500000000000 : ℝ) (188649748379/1000000000000 : ℝ) (37729949677/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1039/8192 : ℝ)) (982044435061/1000000000000 : ℝ) (491022217531/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982044435061/1000000000000 : ℝ) (491022217531/500000000000 : ℝ) (99102221753/100000000000 : ℝ) (991022217531/1000000000000 : ℝ) (495490775661/500000000000 : ℝ) (990981551323/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 1 (99102221753/100000000000 : ℝ) (991022217531/1000000000000 : ℝ) (495490775661/500000000000 : ℝ) (990981551323/1000000000000 : ℝ) (495500942213/500000000000 : ℝ) (991001884427/1000000000000 : ℝ) (991001884217/1000000000000 : ℝ) (991001884219/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 2 (495500942213/500000000000 : ℝ) (991001884427/1000000000000 : ℝ) (991001884217/1000000000000 : ℝ) (991001884219/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 3 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 4 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 5 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 6 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1039/8192 : ℝ)) 7 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1039/8192 : ℝ))) (188649748379/1000000000000 : ℝ) (37729949677/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188649748379/1000000000000 : ℝ) (37729949677/200000000000 : ℝ) (594324874189/1000000000000 : ℝ) (594324874193/1000000000000 : ℝ) (434338287949/1000000000000 : ℝ) (434338287957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 1 (594324874189/1000000000000 : ℝ) (594324874193/1000000000000 : ℝ) (434338287949/1000000000000 : ℝ) (434338287957/1000000000000 : ℝ) (514331581069/1000000000000 : ℝ) (20573263243/40000000000 : ℝ) (508072876997/1000000000000 : ℝ) (101614575401/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 2 (514331581069/1000000000000 : ℝ) (20573263243/40000000000 : ℝ) (508072876997/1000000000000 : ℝ) (101614575401/200000000000 : ℝ) (511202229033/1000000000000 : ℝ) (6390027863/12500000000 : ℝ) (255596325347/500000000000 : ℝ) (255596325351/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 3 (511202229033/1000000000000 : ℝ) (6390027863/12500000000 : ℝ) (255596325347/500000000000 : ℝ) (255596325351/500000000000 : ℝ) (511197439863/1000000000000 : ℝ) (511197439871/1000000000000 : ℝ) (511197439841/1000000000000 : ℝ) (511197439849/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 4 (511197439863/1000000000000 : ℝ) (511197439871/1000000000000 : ℝ) (511197439841/1000000000000 : ℝ) (511197439849/1000000000000 : ℝ) (127799359963/250000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 5 (127799359963/250000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 6 (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1039/8192 : ℝ))) 7 (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1039/8192 : ℝ)) hmem 8 (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1039/8192 : ℝ))) hcmem 8 (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1039/8192 : ℝ)) (991001884321/1000000000000 : ℝ) (991001884323/1000000000000 : ℝ) (511197439851/1000000000000 : ℝ) (25559871993/50000000000 : ℝ) (162055607257/200000000000 : ℝ) (405139018151/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0051_exp_lower
  have heNumeric : (2019248291417/1000000000000 : ℝ)/4 ≤ Real.exp (-683569051927/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019248291417/1000000000000 : ℝ)/4 ≤ Real.exp ((519/4096 : ℝ)-(405139018151/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (519/4096 : ℝ) (1039/8192 : ℝ) (405139018151/500000000000 : ℝ) (2019248291417/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0052; no trusted numerical premise.
theorem cover7_leaf0052_exp_radius : (997735547660010633/1000000000000000000 : ℝ) ≤ Real.exp ((-65/3584 : ℝ)/8) ∧ Real.exp ((-65/3584 : ℝ)/8) ≤ (498867773830005317/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-65/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0052_exp_lower : (57381369820763367/62500000000000000 : ℝ) ≤ Real.exp ((-54685999157/80000000000 : ℝ)/8) ∧ Real.exp ((-54685999157/80000000000 : ℝ)/8) ≤ (918101917132213873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-54685999157/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0052_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009618151047/500000000000 : ℝ) ≤ 4*Real.exp (1039/8192 : ℝ)*Real.exp (-mu (radius 7 (65/512 : ℝ))) ∧ (2019/1000 : ℝ) < (1009618151047/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (65/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0052_exp_radius
  have hrNumeric : (491013654857/500000000000 : ℝ) ≤ Real.exp (-65/3584 : ℝ) ∧ Real.exp (-65/3584 : ℝ) ≤ (196405461943/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491013654857/500000000000 : ℝ) ≤ (radius 7 (65/512 : ℝ)) ∧ (radius 7 (65/512 : ℝ)) ≤ (196405461943/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (65/512 : ℝ)) (491013654857/500000000000 : ℝ) (196405461943/200000000000 : ℝ) (188738875099/1000000000000 : ℝ) (37747775021/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (65/512 : ℝ)) (491013654857/500000000000 : ℝ) (196405461943/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (65/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491013654857/500000000000 : ℝ) (196405461943/200000000000 : ℝ) (991013654857/1000000000000 : ℝ) (495506827429/500000000000 : ℝ) (495486455343/500000000000 : ℝ) (990972910687/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (65/512 : ℝ)) 1 (991013654857/1000000000000 : ℝ) (495506827429/500000000000 : ℝ) (495486455343/500000000000 : ℝ) (990972910687/1000000000000 : ℝ) (990993282771/1000000000000 : ℝ) (990993282773/1000000000000 : ℝ) (495496641281/500000000000 : ℝ) (247748320641/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (65/512 : ℝ)) 2 (990993282771/1000000000000 : ℝ) (990993282773/1000000000000 : ℝ) (495496641281/500000000000 : ℝ) (247748320641/250000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (65/512 : ℝ)) 3 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (65/512 : ℝ)) 4 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (65/512 : ℝ)) 5 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (65/512 : ℝ)) 6 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (65/512 : ℝ)) 7 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (65/512 : ℝ))) (188738875099/1000000000000 : ℝ) (37747775021/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188738875099/1000000000000 : ℝ) (37747775021/200000000000 : ℝ) (594369437549/1000000000000 : ℝ) (594369437553/1000000000000 : ℝ) (434440876413/1000000000000 : ℝ) (434440876421/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 1 (594369437549/1000000000000 : ℝ) (594369437553/1000000000000 : ℝ) (434440876413/1000000000000 : ℝ) (434440876421/1000000000000 : ℝ) (514405156981/1000000000000 : ℝ) (514405156987/1000000000000 : ℝ) (15879747671/31250000000 : ℝ) (12703798137/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 2 (514405156981/1000000000000 : ℝ) (514405156987/1000000000000 : ℝ) (15879747671/31250000000 : ℝ) (12703798137/25000000000 : ℝ) (255639270613/500000000000 : ℝ) (255639270617/500000000000 : ℝ) (255634490529/500000000000 : ℝ) (255634490533/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 3 (255639270613/500000000000 : ℝ) (255639270617/500000000000 : ℝ) (255634490529/500000000000 : ℝ) (255634490533/500000000000 : ℝ) (255636880571/500000000000 : ℝ) (10225475223/20000000000 : ℝ) (511273761119/1000000000000 : ℝ) (63909220141/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 4 (255636880571/500000000000 : ℝ) (10225475223/20000000000 : ℝ) (511273761119/1000000000000 : ℝ) (63909220141/125000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 5 (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 6 (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (65/512 : ℝ))) 7 (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (65/512 : ℝ)) hmem 8 (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (65/512 : ℝ))) hcmem 8 (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (65/512 : ℝ)) (495496641333/500000000000 : ℝ) (990993282669/1000000000000 : ℝ) (51127376113/100000000000 : ℝ) (511273761139/1000000000000 : ℝ) (202601511033/250000000000 : ℝ) (16208120883/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0052_exp_lower
  have heNumeric : (1009618151047/500000000000 : ℝ)/4 ≤ Real.exp (-54685999157/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009618151047/500000000000 : ℝ)/4 ≤ Real.exp ((1039/8192 : ℝ)-(16208120883/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1039/8192 : ℝ) (65/512 : ℝ) (16208120883/20000000000 : ℝ) (1009618151047/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0053; no trusted numerical premise.
theorem cover7_leaf0053_exp_radius : (997733372771486517/1000000000000000000 : ℝ) ≤ Real.exp ((-1041/57344 : ℝ)/8) ∧ Real.exp ((-1041/57344 : ℝ)/8) ≤ (498866686385743259/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1041/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0053_exp_lower : (229525311302038201/250000000000000000 : ℝ) ≤ Real.exp ((-341790422181/500000000000 : ℝ)/8) ∧ Real.exp ((-341790422181/500000000000 : ℝ)/8) ≤ (183620249041630561/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341790422181/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0053_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019224479703/1000000000000 : ℝ) ≤ 4*Real.exp (65/512 : ℝ)*Real.exp (-mu (radius 7 (1041/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019224479703/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1041/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0053_exp_radius
  have hrNumeric : (491005092333/500000000000 : ℝ) ≤ Real.exp (-1041/57344 : ℝ) ∧ Real.exp (-1041/57344 : ℝ) ≤ (982010184667/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491005092333/500000000000 : ℝ) ≤ (radius 7 (1041/8192 : ℝ)) ∧ (radius 7 (1041/8192 : ℝ)) ≤ (982010184667/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1041/8192 : ℝ)) (491005092333/500000000000 : ℝ) (982010184667/1000000000000 : ℝ) (188827956643/1000000000000 : ℝ) (3776559133/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1041/8192 : ℝ)) (491005092333/500000000000 : ℝ) (982010184667/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491005092333/500000000000 : ℝ) (982010184667/1000000000000 : ℝ) (991005092333/1000000000000 : ℝ) (495502546167/500000000000 : ℝ) (7927714161/8000000000 : ℝ) (990964270127/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 1 (991005092333/1000000000000 : ℝ) (495502546167/500000000000 : ℝ) (7927714161/8000000000 : ℝ) (990964270127/1000000000000 : ℝ) (990984681229/1000000000000 : ℝ) (990984681231/1000000000000 : ℝ) (495492340509/500000000000 : ℝ) (990984681021/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 2 (990984681229/1000000000000 : ℝ) (990984681231/1000000000000 : ℝ) (495492340509/500000000000 : ℝ) (990984681021/1000000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 3 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 4 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 5 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 6 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1041/8192 : ℝ)) 7 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1041/8192 : ℝ))) (188827956643/1000000000000 : ℝ) (3776559133/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188827956643/1000000000000 : ℝ) (3776559133/20000000000 : ℝ) (594413978321/1000000000000 : ℝ) (23776559133/40000000000 : ℝ) (434543388677/1000000000000 : ℝ) (217271694343/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 1 (594413978321/1000000000000 : ℝ) (23776559133/40000000000 : ℝ) (434543388677/1000000000000 : ℝ) (217271694343/500000000000 : ℝ) (514478683499/1000000000000 : ℝ) (257239341753/500000000000 : ℝ) (508230916431/1000000000000 : ℝ) (508230916439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 2 (514478683499/1000000000000 : ℝ) (257239341753/500000000000 : ℝ) (508230916431/1000000000000 : ℝ) (508230916439/1000000000000 : ℝ) (102270959993/200000000000 : ℝ) (511354799973/1000000000000 : ℝ) (511345257921/1000000000000 : ℝ) (51134525793/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 3 (102270959993/200000000000 : ℝ) (511354799973/1000000000000 : ℝ) (511345257921/1000000000000 : ℝ) (51134525793/100000000000 : ℝ) (511350028943/1000000000000 : ℝ) (63918753619/125000000000 : ℝ) (12783750723/25000000000 : ℝ) (51135002893/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 4 (511350028943/1000000000000 : ℝ) (63918753619/125000000000 : ℝ) (12783750723/25000000000 : ℝ) (51135002893/100000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 5 (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 6 (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1041/8192 : ℝ))) 7 (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1041/8192 : ℝ)) hmem 8 (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1041/8192 : ℝ))) hcmem 8 (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1041/8192 : ℝ)) (990984681123/1000000000000 : ℝ) (495492340563/500000000000 : ℝ) (511350028931/1000000000000 : ℝ) (511350028941/1000000000000 : ℝ) (810533969343/1000000000000 : ℝ) (405266984681/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0053_exp_lower
  have heNumeric : (2019224479703/1000000000000 : ℝ)/4 ≤ Real.exp (-341790422181/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019224479703/1000000000000 : ℝ)/4 ≤ Real.exp ((65/512 : ℝ)-(405266984681/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (65/512 : ℝ) (1041/8192 : ℝ) (405266984681/500000000000 : ℝ) (2019224479703/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0054; no trusted numerical premise.
theorem cover7_leaf0054_exp_radius : (997731197887703277/1000000000000000000 : ℝ) ≤ Real.exp ((-521/28672 : ℝ)/8) ∧ Real.exp ((-521/28672 : ℝ)/8) ≤ (498865598943851639/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-521/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0054_exp_lower : (918100582752954753/1000000000000000000 : ℝ) ≤ Real.exp ((-273434646703/400000000000 : ℝ)/8) ∧ Real.exp ((-273434646703/400000000000 : ℝ)/8) ≤ (459050291376477377/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273434646703/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0054_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80768512959/40000000000 : ℝ) ≤ 4*Real.exp (1041/8192 : ℝ)*Real.exp (-mu (radius 7 (521/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (80768512959/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (521/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0054_exp_radius
  have hrNumeric : (981993059917/1000000000000 : ℝ) ≤ Real.exp (-521/28672 : ℝ) ∧ Real.exp (-521/28672 : ℝ) ≤ (490996529959/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981993059917/1000000000000 : ℝ) ≤ (radius 7 (521/4096 : ℝ)) ∧ (radius 7 (521/4096 : ℝ)) ≤ (490996529959/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (521/4096 : ℝ)) (981993059917/1000000000000 : ℝ) (490996529959/500000000000 : ℝ) (47229248269/250000000000 : ℝ) (94458496541/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (521/4096 : ℝ)) (981993059917/1000000000000 : ℝ) (490996529959/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (521/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981993059917/1000000000000 : ℝ) (490996529959/500000000000 : ℝ) (495498264979/500000000000 : ℝ) (990996529959/1000000000000 : ℝ) (24773890741/25000000000 : ℝ) (495477814821/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (521/4096 : ℝ)) 1 (495498264979/500000000000 : ℝ) (990996529959/1000000000000 : ℝ) (24773890741/25000000000 : ℝ) (495477814821/500000000000 : ℝ) (990976079799/1000000000000 : ℝ) (990976079801/1000000000000 : ℝ) (990976079587/1000000000000 : ℝ) (99097607959/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (521/4096 : ℝ)) 2 (990976079799/1000000000000 : ℝ) (990976079801/1000000000000 : ℝ) (990976079587/1000000000000 : ℝ) (99097607959/100000000000 : ℝ) (990976079693/1000000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (521/4096 : ℝ)) 3 (990976079693/1000000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (521/4096 : ℝ)) 4 (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (521/4096 : ℝ)) 5 (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (521/4096 : ℝ)) 6 (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (521/4096 : ℝ)) 7 (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (521/4096 : ℝ))) (47229248269/250000000000 : ℝ) (94458496541/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47229248269/250000000000 : ℝ) (94458496541/500000000000 : ℝ) (297229248269/500000000000 : ℝ) (594458496541/1000000000000 : ℝ) (108661456217/250000000000 : ℝ) (108661456219/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 1 (297229248269/500000000000 : ℝ) (594458496541/1000000000000 : ℝ) (108661456217/250000000000 : ℝ) (108661456219/250000000000 : ℝ) (514552160703/1000000000000 : ℝ) (514552160709/1000000000000 : ℝ) (508309849971/1000000000000 : ℝ) (508309849977/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 2 (514552160703/1000000000000 : ℝ) (514552160709/1000000000000 : ℝ) (508309849971/1000000000000 : ℝ) (508309849977/1000000000000 : ℝ) (511431005337/1000000000000 : ℝ) (511431005343/1000000000000 : ℝ) (127855370343/250000000000 : ℝ) (511421481379/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 3 (511431005337/1000000000000 : ℝ) (511431005343/1000000000000 : ℝ) (127855370343/250000000000 : ℝ) (511421481379/1000000000000 : ℝ) (255713121677/500000000000 : ℝ) (511426243361/1000000000000 : ℝ) (127856560833/250000000000 : ℝ) (511426243339/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 4 (255713121677/500000000000 : ℝ) (511426243361/1000000000000 : ℝ) (127856560833/250000000000 : ℝ) (511426243339/1000000000000 : ℝ) (511426243343/1000000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 5 (511426243343/1000000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 6 (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (521/4096 : ℝ))) 7 (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (521/4096 : ℝ)) hmem 8 (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (521/4096 : ℝ))) hcmem 8 (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (521/4096 : ℝ)) (247744019923/250000000000 : ℝ) (61936004981/62500000000 : ℝ) (255713121671/500000000000 : ℝ) (10228524867/20000000000 : ℝ) (810661812053/1000000000000 : ℝ) (81066181207/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0054_exp_lower
  have heNumeric : (80768512959/40000000000 : ℝ)/4 ≤ Real.exp (-273434646703/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80768512959/40000000000 : ℝ)/4 ≤ Real.exp ((1041/8192 : ℝ)-(81066181207/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1041/8192 : ℝ) (521/4096 : ℝ) (81066181207/100000000000 : ℝ) (80768512959/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0055; no trusted numerical premise.
theorem cover7_leaf0055_exp_radius : (997729023008660901/1000000000000000000 : ℝ) ≤ Real.exp ((-149/8192 : ℝ)/8) ∧ Real.exp ((-149/8192 : ℝ)/8) ≤ (498864511504330451/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-149/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0055_exp_lower : (459049964874520281/500000000000000000 : ℝ) ≤ Real.exp ((-341796153401/500000000000 : ℝ)/8) ∧ Real.exp ((-341796153401/500000000000 : ℝ)/8) ≤ (918099929749040563/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341796153401/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0055_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019201334597/1000000000000 : ℝ) ≤ 4*Real.exp (521/4096 : ℝ)*Real.exp (-mu (radius 7 (1043/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019201334597/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1043/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0055_exp_radius
  have hrNumeric : (490987967733/500000000000 : ℝ) ≤ Real.exp (-149/8192 : ℝ) ∧ Real.exp (-149/8192 : ℝ) ≤ (981975935467/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490987967733/500000000000 : ℝ) ≤ (radius 7 (1043/8192 : ℝ)) ∧ (radius 7 (1043/8192 : ℝ)) ≤ (981975935467/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1043/8192 : ℝ)) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1043/8192 : ℝ)) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490987967733/500000000000 : ℝ) (981975935467/1000000000000 : ℝ) (990987967733/1000000000000 : ℝ) (495493983867/500000000000 : ℝ) (990946989231/1000000000000 : ℝ) (61934186827/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 1 (990987967733/1000000000000 : ℝ) (495493983867/500000000000 : ℝ) (990946989231/1000000000000 : ℝ) (61934186827/62500000000 : ℝ) (495483739241/500000000000 : ℝ) (990967478483/1000000000000 : ℝ) (99096747827/100000000000 : ℝ) (483870839/488281250 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 2 (495483739241/500000000000 : ℝ) (990967478483/1000000000000 : ℝ) (99096747827/100000000000 : ℝ) (483870839/488281250 : ℝ) (123870934797/125000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 3 (123870934797/125000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 4 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 5 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 6 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1043/8192 : ℝ)) 7 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1043/8192 : ℝ))) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37801196893/200000000000 : ℝ) (189005984471/1000000000000 : ℝ) (74312874029/125000000000 : ℝ) (148625748059/250000000000 : ℝ) (434748185119/1000000000000 : ℝ) (434748185127/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 1 (74312874029/125000000000 : ℝ) (148625748059/250000000000 : ℝ) (434748185119/1000000000000 : ℝ) (434748185127/1000000000000 : ℝ) (20585023547/40000000000 : ℝ) (257312794341/500000000000 : ℝ) (508388726193/1000000000000 : ℝ) (2541943631/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 2 (20585023547/40000000000 : ℝ) (257312794341/500000000000 : ℝ) (508388726193/1000000000000 : ℝ) (2541943631/5000000000 : ℝ) (255753578717/500000000000 : ℝ) (511507157441/1000000000000 : ℝ) (255748825751/500000000000 : ℝ) (51149765151/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 3 (255753578717/500000000000 : ℝ) (511507157441/1000000000000 : ℝ) (255748825751/500000000000 : ℝ) (51149765151/100000000000 : ℝ) (127875601117/250000000000 : ℝ) (127875601119/250000000000 : ℝ) (102300480889/200000000000 : ℝ) (255751202227/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 4 (127875601117/250000000000 : ℝ) (127875601119/250000000000 : ℝ) (102300480889/200000000000 : ℝ) (255751202227/500000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 5 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 6 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1043/8192 : ℝ))) 7 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1043/8192 : ℝ)) hmem 8 (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1043/8192 : ℝ))) hcmem 8 (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1043/8192 : ℝ)) (7927739827/8000000000 : ℝ) (495483739189/500000000000 : ℝ) (63937800557/125000000000 : ℝ) (102300480893/200000000000 : ℝ) (810789572409/1000000000000 : ℝ) (810789572427/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0055_exp_lower
  have heNumeric : (2019201334597/1000000000000 : ℝ)/4 ≤ Real.exp (-341796153401/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019201334597/1000000000000 : ℝ)/4 ≤ Real.exp ((521/4096 : ℝ)-(810789572427/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (521/4096 : ℝ) (1043/8192 : ℝ) (810789572427/1000000000000 : ℝ) (2019201334597/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0056; no trusted numerical premise.
theorem cover7_leaf0056_exp_radius : (997726848134359381/1000000000000000000 : ℝ) ≤ Real.exp ((-261/14336 : ℝ)/8) ∧ Real.exp ((-261/14336 : ℝ)/8) ≤ (498863424067179691/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-261/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0056_exp_lower : (918099286181470951/1000000000000000000 : ℝ) ≤ Real.exp ((-1367195829251/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367195829251/2000000000000 : ℝ)/8) ≤ (114762410772683869/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367195829251/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0056_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252398751413/125000000000 : ℝ) ≤ 4*Real.exp (1043/8192 : ℝ)*Real.exp (-mu (radius 7 (261/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (252398751413/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (261/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0056_exp_radius
  have hrNumeric : (490979405657/500000000000 : ℝ) ≤ Real.exp (-261/14336 : ℝ) ∧ Real.exp (-261/14336 : ℝ) ≤ (196391762263/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490979405657/500000000000 : ℝ) ≤ (radius 7 (261/2048 : ℝ)) ∧ (radius 7 (261/2048 : ℝ)) ≤ (196391762263/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (261/2048 : ℝ)) (490979405657/500000000000 : ℝ) (196391762263/200000000000 : ℝ) (18909493087/100000000000 : ℝ) (47273732719/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (261/2048 : ℝ)) (490979405657/500000000000 : ℝ) (196391762263/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (261/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490979405657/500000000000 : ℝ) (196391762263/200000000000 : ℝ) (990979405657/1000000000000 : ℝ) (495489702829/500000000000 : ℝ) (30966823403/31250000000 : ℝ) (495469174449/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (261/2048 : ℝ)) 1 (990979405657/1000000000000 : ℝ) (495489702829/500000000000 : ℝ) (30966823403/31250000000 : ℝ) (495469174449/500000000000 : ℝ) (247739719319/250000000000 : ℝ) (495479438639/500000000000 : ℝ) (990958877063/1000000000000 : ℝ) (495479438533/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (261/2048 : ℝ)) 2 (247739719319/250000000000 : ℝ) (495479438639/500000000000 : ℝ) (990958877063/1000000000000 : ℝ) (495479438533/500000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (261/2048 : ℝ)) 3 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (261/2048 : ℝ)) 4 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (261/2048 : ℝ)) 5 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (261/2048 : ℝ)) 6 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (261/2048 : ℝ)) 7 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (261/2048 : ℝ))) (18909493087/100000000000 : ℝ) (47273732719/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18909493087/100000000000 : ℝ) (47273732719/250000000000 : ℝ) (118909493087/200000000000 : ℝ) (297273732719/500000000000 : ℝ) (27178154347/62500000000 : ℝ) (10871261739/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 1 (118909493087/200000000000 : ℝ) (297273732719/500000000000 : ℝ) (27178154347/62500000000 : ℝ) (10871261739/25000000000 : ℝ) (514698967493/1000000000000 : ℝ) (514698967499/1000000000000 : ℝ) (508467545193/1000000000000 : ℝ) (1271168863/2500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 2 (514698967493/1000000000000 : ℝ) (514698967499/1000000000000 : ℝ) (508467545193/1000000000000 : ℝ) (1271168863/2500000000 : ℝ) (511583256343/1000000000000 : ℝ) (10231665127/20000000000 : ℝ) (511573768399/1000000000000 : ℝ) (511573768407/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 3 (511583256343/1000000000000 : ℝ) (10231665127/20000000000 : ℝ) (511573768399/1000000000000 : ℝ) (511573768407/1000000000000 : ℝ) (511578512371/1000000000000 : ℝ) (511578512379/1000000000000 : ℝ) (511578512349/1000000000000 : ℝ) (511578512357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 4 (511578512371/1000000000000 : ℝ) (511578512379/1000000000000 : ℝ) (511578512349/1000000000000 : ℝ) (511578512357/1000000000000 : ℝ) (12789462809/25000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 5 (12789462809/25000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 6 (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (261/2048 : ℝ))) 7 (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (261/2048 : ℝ)) hmem 8 (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (261/2048 : ℝ))) hcmem 8 (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (261/2048 : ℝ)) (990958877169/1000000000000 : ℝ) (247739719293/250000000000 : ℝ) (511578512359/1000000000000 : ℝ) (31973657023/62500000000 : ℝ) (405458625273/500000000000 : ℝ) (810917250563/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0056_exp_lower
  have heNumeric : (252398751413/125000000000 : ℝ)/4 ≤ Real.exp (-1367195829251/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252398751413/125000000000 : ℝ)/4 ≤ Real.exp ((1043/8192 : ℝ)-(810917250563/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1043/8192 : ℝ) (261/2048 : ℝ) (810917250563/1000000000000 : ℝ) (252398751413/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0057; no trusted numerical premise.
theorem cover7_leaf0057_exp_radius : (199544934652959741/200000000000000000 : ℝ) ≤ Real.exp ((-1045/57344 : ℝ)/8) ∧ Real.exp ((-1045/57344 : ℝ)/8) ≤ (498862336632399353/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1045/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0057_exp_lower : (918098652034503637/1000000000000000000 : ℝ) ≤ Real.exp ((-136720688073/200000000000 : ℝ)/8) ∧ Real.exp ((-136720688073/200000000000 : ℝ)/8) ≤ (459049326017251819/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136720688073/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0057_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252397356727/125000000000 : ℝ) ≤ 4*Real.exp (261/2048 : ℝ)*Real.exp (-mu (radius 7 (1045/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (252397356727/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1045/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0057_exp_radius
  have hrNumeric : (981941687461/1000000000000 : ℝ) ≤ Real.exp (-1045/57344 : ℝ) ∧ Real.exp (-1045/57344 : ℝ) ≤ (490970843731/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981941687461/1000000000000 : ℝ) ≤ (radius 7 (1045/8192 : ℝ)) ∧ (radius 7 (1045/8192 : ℝ)) ≤ (490970843731/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1045/8192 : ℝ)) (981941687461/1000000000000 : ℝ) (490970843731/500000000000 : ℝ) (94591916177/500000000000 : ℝ) (4729595809/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1045/8192 : ℝ)) (981941687461/1000000000000 : ℝ) (490970843731/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981941687461/1000000000000 : ℝ) (490970843731/500000000000 : ℝ) (99097084373/100000000000 : ℝ) (990970843731/1000000000000 : ℝ) (990929708637/1000000000000 : ℝ) (990929708639/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 1 (99097084373/100000000000 : ℝ) (990970843731/1000000000000 : ℝ) (990929708637/1000000000000 : ℝ) (990929708639/1000000000000 : ℝ) (990950276183/1000000000000 : ℝ) (198190055237/200000000000 : ℝ) (99095027597/100000000000 : ℝ) (247737568993/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 2 (990950276183/1000000000000 : ℝ) (198190055237/200000000000 : ℝ) (99095027597/100000000000 : ℝ) (247737568993/250000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 3 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 4 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 5 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 6 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1045/8192 : ℝ)) 7 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1045/8192 : ℝ))) (94591916177/500000000000 : ℝ) (4729595809/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94591916177/500000000000 : ℝ) (4729595809/25000000000 : ℝ) (594591916177/1000000000000 : ℝ) (29729595809/50000000000 : ℝ) (108738169573/250000000000 : ℝ) (4349526783/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 1 (594591916177/1000000000000 : ℝ) (29729595809/50000000000 : ℝ) (108738169573/250000000000 : ℝ) (4349526783/10000000000 : ℝ) (257386148617/500000000000 : ℝ) (12869307431/25000000000 : ℝ) (508546307067/1000000000000 : ℝ) (254273153537/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 2 (257386148617/500000000000 : ℝ) (12869307431/25000000000 : ℝ) (508546307067/1000000000000 : ℝ) (254273153537/500000000000 : ℝ) (10233186043/20000000000 : ℝ) (511659302157/1000000000000 : ℝ) (511649832149/1000000000000 : ℝ) (511649832157/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 3 (10233186043/20000000000 : ℝ) (511659302157/1000000000000 : ℝ) (511649832149/1000000000000 : ℝ) (511649832157/1000000000000 : ℝ) (511654567149/1000000000000 : ℝ) (511654567157/1000000000000 : ℝ) (511654567127/1000000000000 : ℝ) (15989205223/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 4 (511654567149/1000000000000 : ℝ) (511654567157/1000000000000 : ℝ) (511654567127/1000000000000 : ℝ) (15989205223/31250000000 : ℝ) (255827283569/500000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 5 (255827283569/500000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 6 (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1045/8192 : ℝ))) 7 (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1045/8192 : ℝ)) hmem 8 (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1045/8192 : ℝ))) hcmem 8 (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1045/8192 : ℝ)) (247737569019/250000000000 : ℝ) (990950276079/1000000000000 : ℝ) (511654567137/1000000000000 : ℝ) (511654567147/1000000000000 : ℝ) (162208969319/200000000000 : ℝ) (162208969323/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0057_exp_lower
  have heNumeric : (252397356727/125000000000 : ℝ)/4 ≤ Real.exp (-136720688073/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252397356727/125000000000 : ℝ)/4 ≤ Real.exp ((261/2048 : ℝ)-(162208969323/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (261/2048 : ℝ) (1045/8192 : ℝ) (162208969323/200000000000 : ℝ) (252397356727/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0058; no trusted numerical premise.
theorem cover7_leaf0058_exp_radius : (997722498399978863/1000000000000000000 : ℝ) ≤ Real.exp ((-523/28672 : ℝ)/8) ∧ Real.exp ((-523/28672 : ℝ)/8) ≤ (62357656149998679/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-523/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0058_exp_lower : (114762253411449167/125000000000000000 : ℝ) ≤ Real.exp ((-1367217768329/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367217768329/2000000000000 : ℝ)/8) ≤ (918098027291593337/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367217768329/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0058_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019167861841/1000000000000 : ℝ) ≤ 4*Real.exp (1045/8192 : ℝ)*Real.exp (-mu (radius 7 (523/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019167861841/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (523/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0058_exp_radius
  have hrNumeric : (490962281953/500000000000 : ℝ) ≤ Real.exp (-523/28672 : ℝ) ∧ Real.exp (-523/28672 : ℝ) ≤ (981924563907/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490962281953/500000000000 : ℝ) ≤ (radius 7 (523/4096 : ℝ)) ∧ (radius 7 (523/4096 : ℝ)) ≤ (981924563907/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (523/4096 : ℝ)) (490962281953/500000000000 : ℝ) (981924563907/1000000000000 : ℝ) (94636344493/500000000000 : ℝ) (5914771531/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (523/4096 : ℝ)) (490962281953/500000000000 : ℝ) (981924563907/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (523/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490962281953/500000000000 : ℝ) (981924563907/1000000000000 : ℝ) (990962281953/1000000000000 : ℝ) (495481140977/500000000000 : ℝ) (990921068453/1000000000000 : ℝ) (198184213691/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (523/4096 : ℝ)) 1 (990962281953/1000000000000 : ℝ) (495481140977/500000000000 : ℝ) (990921068453/1000000000000 : ℝ) (198184213691/200000000000 : ℝ) (990941675203/1000000000000 : ℝ) (198188335041/200000000000 : ℝ) (247735418747/250000000000 : ℝ) (990941674991/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (523/4096 : ℝ)) 2 (990941675203/1000000000000 : ℝ) (198188335041/200000000000 : ℝ) (247735418747/250000000000 : ℝ) (990941674991/1000000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (523/4096 : ℝ)) 3 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (523/4096 : ℝ)) 4 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (523/4096 : ℝ)) 5 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (523/4096 : ℝ)) 6 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (523/4096 : ℝ)) 7 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (523/4096 : ℝ))) (94636344493/500000000000 : ℝ) (5914771531/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94636344493/500000000000 : ℝ) (5914771531/31250000000 : ℝ) (594636344493/1000000000000 : ℝ) (37164771531/62500000000 : ℝ) (435054811473/1000000000000 : ℝ) (435054811481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 1 (594636344493/1000000000000 : ℝ) (37164771531/62500000000 : ℝ) (435054811473/1000000000000 : ℝ) (435054811481/1000000000000 : ℝ) (514845577983/1000000000000 : ℝ) (514845577989/1000000000000 : ℝ) (508625011917/1000000000000 : ℝ) (127156252981/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 2 (514845577983/1000000000000 : ℝ) (514845577989/1000000000000 : ℝ) (508625011917/1000000000000 : ℝ) (127156252981/250000000000 : ℝ) (10234705899/20000000000 : ℝ) (511735294957/1000000000000 : ℝ) (255862921423/500000000000 : ℝ) (255862921427/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 3 (10234705899/20000000000 : ℝ) (511735294957/1000000000000 : ℝ) (255862921423/500000000000 : ℝ) (255862921427/500000000000 : ℝ) (255865284449/500000000000 : ℝ) (255865284453/500000000000 : ℝ) (127932642219/250000000000 : ℝ) (127932642221/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 4 (255865284449/500000000000 : ℝ) (255865284453/500000000000 : ℝ) (127932642219/250000000000 : ℝ) (127932642221/250000000000 : ℝ) (511730568887/1000000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 5 (511730568887/1000000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 6 (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (523/4096 : ℝ))) 7 (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (523/4096 : ℝ)) hmem 8 (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (523/4096 : ℝ))) hcmem 8 (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (523/4096 : ℝ)) (198188335019/200000000000 : ℝ) (495470837549/500000000000 : ℝ) (255865284443/500000000000 : ℝ) (102346113779/200000000000 : ℝ) (811172360709/1000000000000 : ℝ) (811172360727/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0058_exp_lower
  have heNumeric : (2019167861841/1000000000000 : ℝ)/4 ≤ Real.exp (-1367217768329/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019167861841/1000000000000 : ℝ)/4 ≤ Real.exp ((1045/8192 : ℝ)-(811172360727/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1045/8192 : ℝ) (523/4096 : ℝ) (811172360727/1000000000000 : ℝ) (2019167861841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0059; no trusted numerical premise.
theorem cover7_leaf0059_exp_radius : (498860161769949923/500000000000000000 : ℝ) ≤ Real.exp ((-1047/57344 : ℝ)/8) ∧ Real.exp ((-1047/57344 : ℝ)/8) ≤ (997720323539899847/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1047/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0059_exp_lower : (91809741193791653/100000000000000000 : ℝ) ≤ Real.exp ((-683614246153/1000000000000 : ℝ)/8) ∧ Real.exp ((-683614246153/1000000000000 : ℝ)/8) ≤ (918097411937916531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683614246153/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0059_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504789258779/250000000000 : ℝ) ≤ 4*Real.exp (523/4096 : ℝ)*Real.exp (-mu (radius 7 (1047/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504789258779/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1047/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0059_exp_radius
  have hrNumeric : (19638148813/20000000000 : ℝ) ≤ Real.exp (-1047/57344 : ℝ) ∧ Real.exp (-1047/57344 : ℝ) ≤ (981907440651/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19638148813/20000000000 : ℝ) ≤ (radius 7 (1047/8192 : ℝ)) ∧ (radius 7 (1047/8192 : ℝ)) ≤ (981907440651/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1047/8192 : ℝ)) (19638148813/20000000000 : ℝ) (981907440651/1000000000000 : ℝ) (189361500823/1000000000000 : ℝ) (189361500829/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1047/8192 : ℝ)) (19638148813/20000000000 : ℝ) (981907440651/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19638148813/20000000000 : ℝ) (981907440651/1000000000000 : ℝ) (39638148813/40000000000 : ℝ) (495476860163/500000000000 : ℝ) (198182485669/200000000000 : ℝ) (990912428347/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 1 (39638148813/40000000000 : ℝ) (495476860163/500000000000 : ℝ) (198182485669/200000000000 : ℝ) (990912428347/1000000000000 : ℝ) (198186614867/200000000000 : ℝ) (990933074337/1000000000000 : ℝ) (990933074119/1000000000000 : ℝ) (495466537061/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 2 (198186614867/200000000000 : ℝ) (990933074337/1000000000000 : ℝ) (990933074119/1000000000000 : ℝ) (495466537061/500000000000 : ℝ) (990933074227/1000000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 3 (990933074227/1000000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 4 (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 5 (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 6 (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1047/8192 : ℝ)) 7 (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1047/8192 : ℝ))) (189361500823/1000000000000 : ℝ) (189361500829/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (189361500823/1000000000000 : ℝ) (189361500829/1000000000000 : ℝ) (594680750411/1000000000000 : ℝ) (118936150083/200000000000 : ℝ) (108789217303/250000000000 : ℝ) (21757843461/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 1 (594680750411/1000000000000 : ℝ) (118936150083/200000000000 : ℝ) (108789217303/250000000000 : ℝ) (21757843461/50000000000 : ℝ) (514918809811/1000000000000 : ℝ) (257459404909/500000000000 : ℝ) (254351829917/500000000000 : ℝ) (254351829921/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 2 (514918809811/1000000000000 : ℝ) (257459404909/500000000000 : ℝ) (254351829917/500000000000 : ℝ) (254351829921/500000000000 : ℝ) (255905617411/500000000000 : ℝ) (51181123483/100000000000 : ℝ) (511801800571/1000000000000 : ℝ) (511801800579/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 3 (255905617411/500000000000 : ℝ) (51181123483/100000000000 : ℝ) (511801800571/1000000000000 : ℝ) (511801800579/1000000000000 : ℝ) (7996976839/15625000000 : ℝ) (102361303541/200000000000 : ℝ) (255903258837/500000000000 : ℝ) (511806517683/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 4 (7996976839/15625000000 : ℝ) (102361303541/200000000000 : ℝ) (255903258837/500000000000 : ℝ) (511806517683/1000000000000 : ℝ) (102361303537/200000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 5 (102361303537/200000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 6 (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1047/8192 : ℝ))) 7 (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1047/8192 : ℝ)) hmem 8 (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1047/8192 : ℝ))) hcmem 8 (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1047/8192 : ℝ)) (495466537113/500000000000 : ℝ) (99093307423/100000000000 : ℝ) (127951629421/250000000000 : ℝ) (255903258847/500000000000 : ℝ) (50706237063/62500000000 : ℝ) (202824948257/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0059_exp_lower
  have heNumeric : (504789258779/250000000000 : ℝ)/4 ≤ Real.exp (-683614246153/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504789258779/250000000000 : ℝ)/4 ≤ Real.exp ((523/4096 : ℝ)-(202824948257/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (523/4096 : ℝ) (1047/8192 : ℝ) (202824948257/250000000000 : ℝ) (504789258779/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0060; no trusted numerical premise.
theorem cover7_leaf0060_exp_radius : (997718148684561641/1000000000000000000 : ℝ) ≤ Real.exp ((-131/7168 : ℝ)/8) ∧ Real.exp ((-131/7168 : ℝ)/8) ≤ (498859074342280821/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-131/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0060_exp_lower : (918096805956584311/1000000000000000000 : ℝ) ≤ Real.exp ((-273447810591/400000000000 : ℝ)/8) ∧ Real.exp ((-273447810591/400000000000 : ℝ)/8) ≤ (114762100744573039/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273447810591/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0060_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019146373339/1000000000000 : ℝ) ≤ 4*Real.exp (1047/8192 : ℝ)*Real.exp (-mu (radius 7 (131/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019146373339/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (131/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0060_exp_radius
  have hrNumeric : (245472579423/250000000000 : ℝ) ≤ Real.exp (-131/7168 : ℝ) ∧ Real.exp (-131/7168 : ℝ) ≤ (981890317693/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245472579423/250000000000 : ℝ) ≤ (radius 7 (131/1024 : ℝ)) ∧ (radius 7 (131/1024 : ℝ)) ≤ (981890317693/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (131/1024 : ℝ)) (245472579423/250000000000 : ℝ) (981890317693/1000000000000 : ℝ) (37890053587/200000000000 : ℝ) (189450267941/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (131/1024 : ℝ)) (245472579423/250000000000 : ℝ) (981890317693/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (131/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245472579423/250000000000 : ℝ) (981890317693/1000000000000 : ℝ) (495472579423/500000000000 : ℝ) (990945158847/1000000000000 : ℝ) (123862973539/125000000000 : ℝ) (990903788313/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (131/1024 : ℝ)) 1 (495472579423/500000000000 : ℝ) (990945158847/1000000000000 : ℝ) (123862973539/125000000000 : ℝ) (990903788313/1000000000000 : ℝ) (990924473579/1000000000000 : ℝ) (49546223679/50000000000 : ℝ) (990924473363/1000000000000 : ℝ) (198184894673/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (131/1024 : ℝ)) 2 (990924473579/1000000000000 : ℝ) (49546223679/50000000000 : ℝ) (990924473363/1000000000000 : ℝ) (198184894673/200000000000 : ℝ) (990924473471/1000000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (131/1024 : ℝ)) 3 (990924473471/1000000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (131/1024 : ℝ)) 4 (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (131/1024 : ℝ)) 5 (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (131/1024 : ℝ)) 6 (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (131/1024 : ℝ)) 7 (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (131/1024 : ℝ))) (37890053587/200000000000 : ℝ) (189450267941/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37890053587/200000000000 : ℝ) (189450267941/1000000000000 : ℝ) (594725133967/1000000000000 : ℝ) (594725133971/1000000000000 : ℝ) (108814712911/250000000000 : ℝ) (108814712913/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 1 (594725133967/1000000000000 : ℝ) (594725133971/1000000000000 : ℝ) (108814712911/250000000000 : ℝ) (108814712913/250000000000 : ℝ) (102998398561/200000000000 : ℝ) (128747998203/250000000000 : ℝ) (508782250923/1000000000000 : ℝ) (50878225093/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 2 (102998398561/200000000000 : ℝ) (128747998203/250000000000 : ℝ) (508782250923/1000000000000 : ℝ) (50878225093/100000000000 : ℝ) (63985890233/125000000000 : ℝ) (511887121871/1000000000000 : ℝ) (25593885271/50000000000 : ℝ) (127969426357/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 3 (63985890233/125000000000 : ℝ) (511887121871/1000000000000 : ℝ) (25593885271/50000000000 : ℝ) (127969426357/250000000000 : ℝ) (255941206821/500000000000 : ℝ) (10237648273/20000000000 : ℝ) (25594120681/50000000000 : ℝ) (127970603407/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 4 (255941206821/500000000000 : ℝ) (10237648273/20000000000 : ℝ) (25594120681/50000000000 : ℝ) (127970603407/250000000000 : ℝ) (511882413631/1000000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 5 (511882413631/1000000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 6 (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (131/1024 : ℝ))) 7 (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (131/1024 : ℝ)) hmem 8 (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (131/1024 : ℝ))) hcmem 8 (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (131/1024 : ℝ)) (99092447347/100000000000 : ℝ) (990924473473/1000000000000 : ℝ) (51188241363/100000000000 : ℝ) (511882413639/1000000000000 : ℝ) (811427143647/1000000000000 : ℝ) (162285428733/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0060_exp_lower
  have heNumeric : (2019146373339/1000000000000 : ℝ)/4 ≤ Real.exp (-273447810591/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019146373339/1000000000000 : ℝ)/4 ≤ Real.exp ((1047/8192 : ℝ)-(162285428733/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1047/8192 : ℝ) (131/1024 : ℝ) (162285428733/200000000000 : ℝ) (2019146373339/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0061; no trusted numerical premise.
theorem cover7_leaf0061_exp_radius : (12471449672924553/12500000000000000 : ℝ) ≤ Real.exp ((-1049/57344 : ℝ)/8) ∧ Real.exp ((-1049/57344 : ℝ)/8) ≤ (997715973833964241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1049/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0061_exp_lower : (918096209332888581/1000000000000000000 : ℝ) ≤ Real.exp ((-341812362633/500000000000 : ℝ)/8) ∧ Real.exp ((-341812362633/500000000000 : ℝ)/8) ≤ (459048104666444291/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341812362633/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0061_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504783969063/250000000000 : ℝ) ≤ 4*Real.exp (131/1024 : ℝ)*Real.exp (-mu (radius 7 (1049/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504783969063/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1049/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0061_exp_radius
  have hrNumeric : (981873195033/1000000000000 : ℝ) ≤ Real.exp (-1049/57344 : ℝ) ∧ Real.exp (-1049/57344 : ℝ) ≤ (490936597517/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981873195033/1000000000000 : ℝ) ≤ (radius 7 (1049/8192 : ℝ)) ∧ (radius 7 (1049/8192 : ℝ)) ≤ (490936597517/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1049/8192 : ℝ)) (981873195033/1000000000000 : ℝ) (490936597517/500000000000 : ℝ) (94769495189/500000000000 : ℝ) (11846186899/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1049/8192 : ℝ)) (981873195033/1000000000000 : ℝ) (490936597517/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981873195033/1000000000000 : ℝ) (490936597517/500000000000 : ℝ) (247734149379/250000000000 : ℝ) (990936597517/1000000000000 : ℝ) (495447574177/500000000000 : ℝ) (247723787089/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 1 (247734149379/250000000000 : ℝ) (990936597517/1000000000000 : ℝ) (495447574177/500000000000 : ℝ) (247723787089/250000000000 : ℝ) (198183174587/200000000000 : ℝ) (990915872937/1000000000000 : ℝ) (495457936359/500000000000 : ℝ) (12386448409/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 2 (198183174587/200000000000 : ℝ) (990915872937/1000000000000 : ℝ) (495457936359/500000000000 : ℝ) (12386448409/12500000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 3 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 4 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 5 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 6 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1049/8192 : ℝ)) 7 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1049/8192 : ℝ))) (94769495189/500000000000 : ℝ) (11846186899/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94769495189/500000000000 : ℝ) (11846186899/62500000000 : ℝ) (594769495189/1000000000000 : ℝ) (74346186899/125000000000 : ℝ) (217680379443/500000000000 : ℝ) (217680379447/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 1 (594769495189/1000000000000 : ℝ) (74346186899/125000000000 : ℝ) (217680379443/500000000000 : ℝ) (217680379447/500000000000 : ℝ) (515065127037/1000000000000 : ℝ) (515065127043/1000000000000 : ℝ) (63607598159/125000000000 : ℝ) (508860785279/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 2 (515065127037/1000000000000 : ℝ) (515065127043/1000000000000 : ℝ) (63607598159/125000000000 : ℝ) (508860785279/1000000000000 : ℝ) (255981478077/500000000000 : ℝ) (511962956161/1000000000000 : ℝ) (511953557473/1000000000000 : ℝ) (511953557481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 3 (255981478077/500000000000 : ℝ) (511962956161/1000000000000 : ℝ) (511953557473/1000000000000 : ℝ) (511953557481/1000000000000 : ℝ) (511958256813/1000000000000 : ℝ) (511958256821/1000000000000 : ℝ) (511958256791/1000000000000 : ℝ) (639947821/1250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 4 (511958256813/1000000000000 : ℝ) (511958256821/1000000000000 : ℝ) (511958256791/1000000000000 : ℝ) (639947821/1250000000 : ℝ) (255979128401/500000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 5 (255979128401/500000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 6 (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1049/8192 : ℝ))) 7 (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1049/8192 : ℝ)) hmem 8 (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1049/8192 : ℝ))) hcmem 8 (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1049/8192 : ℝ)) (495457936413/500000000000 : ℝ) (990915872829/1000000000000 : ℝ) (511958256801/1000000000000 : ℝ) (511958256811/1000000000000 : ℝ) (405777206373/500000000000 : ℝ) (405777206383/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0061_exp_lower
  have heNumeric : (504783969063/250000000000 : ℝ)/4 ≤ Real.exp (-341812362633/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504783969063/250000000000 : ℝ)/4 ≤ Real.exp ((131/1024 : ℝ)-(405777206383/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (131/1024 : ℝ) (1049/8192 : ℝ) (405777206383/500000000000 : ℝ) (504783969063/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0062; no trusted numerical premise.
theorem cover7_leaf0062_exp_radius : (62357112436756727/62500000000000000 : ℝ) ≤ Real.exp ((-75/4096 : ℝ)/8) ∧ Real.exp ((-75/4096 : ℝ)/8) ≤ (997713798988107633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-75/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0062_exp_lower : (229523905512829559/250000000000000000 : ℝ) ≤ Real.exp ((-1367259685307/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367259685307/2000000000000 : ℝ)/8) ≤ (918095622051318237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367259685307/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0062_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009562771789/500000000000 : ℝ) ≤ 4*Real.exp (1049/8192 : ℝ)*Real.exp (-mu (radius 7 (525/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009562771789/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (525/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0062_exp_radius
  have hrNumeric : (981856072673/1000000000000 : ℝ) ≤ Real.exp (-75/4096 : ℝ) ∧ Real.exp (-75/4096 : ℝ) ≤ (490928036337/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981856072673/1000000000000 : ℝ) ≤ (radius 7 (525/4096 : ℝ)) ∧ (radius 7 (525/4096 : ℝ)) ≤ (490928036337/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (525/4096 : ℝ)) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (525/4096 : ℝ)) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (525/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981856072673/1000000000000 : ℝ) (490928036337/500000000000 : ℝ) (61933002271/62500000000 : ℝ) (990928036337/1000000000000 : ℝ) (123860813559/125000000000 : ℝ) (495443254237/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (525/4096 : ℝ)) 1 (61933002271/62500000000 : ℝ) (990928036337/1000000000000 : ℝ) (123860813559/125000000000 : ℝ) (495443254237/500000000000 : ℝ) (247726818101/250000000000 : ℝ) (495453636203/500000000000 : ℝ) (495453636093/500000000000 : ℝ) (247726818047/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (525/4096 : ℝ)) 2 (247726818101/250000000000 : ℝ) (495453636203/500000000000 : ℝ) (495453636093/500000000000 : ℝ) (247726818047/250000000000 : ℝ) (198181454459/200000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (525/4096 : ℝ)) 3 (198181454459/200000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (525/4096 : ℝ)) 4 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (525/4096 : ℝ)) 5 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (525/4096 : ℝ)) 6 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (525/4096 : ℝ)) 7 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (525/4096 : ℝ))) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (23703458527/125000000000 : ℝ) (94813834111/500000000000 : ℝ) (148703458527/250000000000 : ℝ) (594813834111/1000000000000 : ℝ) (435462591063/1000000000000 : ℝ) (435462591071/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 1 (148703458527/250000000000 : ℝ) (594813834111/1000000000000 : ℝ) (435462591063/1000000000000 : ℝ) (435462591071/1000000000000 : ℝ) (103027642517/200000000000 : ℝ) (515138212591/1000000000000 : ℝ) (254469631489/500000000000 : ℝ) (101787852597/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 2 (103027642517/200000000000 : ℝ) (515138212591/1000000000000 : ℝ) (254469631489/500000000000 : ℝ) (101787852597/200000000000 : ℝ) (512038737781/1000000000000 : ℝ) (128009684447/250000000000 : ℝ) (512029356819/1000000000000 : ℝ) (256014678413/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 3 (512038737781/1000000000000 : ℝ) (128009684447/250000000000 : ℝ) (512029356819/1000000000000 : ℝ) (256014678413/500000000000 : ℝ) (5120340473/10000000000 : ℝ) (512034047307/1000000000000 : ℝ) (256017023639/500000000000 : ℝ) (256017023643/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 4 (5120340473/10000000000 : ℝ) (512034047307/1000000000000 : ℝ) (256017023639/500000000000 : ℝ) (256017023643/500000000000 : ℝ) (512034047289/1000000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 5 (512034047289/1000000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 6 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (525/4096 : ℝ))) 7 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (525/4096 : ℝ)) hmem 8 (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (525/4096 : ℝ))) hcmem 8 (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (525/4096 : ℝ)) (495453636147/500000000000 : ℝ) (990907272297/1000000000000 : ℝ) (64004255911/125000000000 : ℝ) (512034047297/1000000000000 : ℝ) (12682525007/15625000000 : ℝ) (405840800233/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0062_exp_lower
  have heNumeric : (1009562771789/500000000000 : ℝ)/4 ≤ Real.exp (-1367259685307/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009562771789/500000000000 : ℝ)/4 ≤ Real.exp ((1049/8192 : ℝ)-(405840800233/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1049/8192 : ℝ) (525/4096 : ℝ) (405840800233/500000000000 : ℝ) (1009562771789/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0063; no trusted numerical premise.
theorem cover7_leaf0063_exp_radius : (997711624146991807/1000000000000000000 : ℝ) ≤ Real.exp ((-1051/57344 : ℝ)/8) ∧ Real.exp ((-1051/57344 : ℝ)/8) ≤ (15589244127296747/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1051/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0063_exp_lower : (229523761023832409/250000000000000000 : ℝ) ≤ Real.exp ((-10681794981/15625000000 : ℝ)/8) ∧ Real.exp ((-10681794981/15625000000 : ℝ)/8) ≤ (918095044095329637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10681794981/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0063_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019115375023/1000000000000 : ℝ) ≤ 4*Real.exp (525/4096 : ℝ)*Real.exp (-mu (radius 7 (1051/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019115375023/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1051/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0063_exp_radius
  have hrNumeric : (981838950611/1000000000000 : ℝ) ≤ Real.exp (-1051/57344 : ℝ) ∧ Real.exp (-1051/57344 : ℝ) ≤ (245459737653/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981838950611/1000000000000 : ℝ) ≤ (radius 7 (1051/8192 : ℝ)) ∧ (radius 7 (1051/8192 : ℝ)) ≤ (245459737653/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1051/8192 : ℝ)) (981838950611/1000000000000 : ℝ) (245459737653/250000000000 : ℝ) (47429075379/250000000000 : ℝ) (94858150761/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1051/8192 : ℝ)) (981838950611/1000000000000 : ℝ) (245459737653/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981838950611/1000000000000 : ℝ) (245459737653/250000000000 : ℝ) (198183895061/200000000000 : ℝ) (495459737653/500000000000 : ℝ) (198175573733/200000000000 : ℝ) (495438934333/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 1 (198183895061/200000000000 : ℝ) (495459737653/500000000000 : ℝ) (198175573733/200000000000 : ℝ) (495438934333/500000000000 : ℝ) (198179734397/200000000000 : ℝ) (495449335993/500000000000 : ℝ) (495449335883/500000000000 : ℝ) (123862333971/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 2 (198179734397/200000000000 : ℝ) (495449335993/500000000000 : ℝ) (495449335883/500000000000 : ℝ) (123862333971/125000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 3 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 4 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 5 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 6 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1051/8192 : ℝ)) 7 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1051/8192 : ℝ))) (47429075379/250000000000 : ℝ) (94858150761/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47429075379/250000000000 : ℝ) (94858150761/500000000000 : ℝ) (297429075379/500000000000 : ℝ) (594858150761/1000000000000 : ℝ) (217782174153/500000000000 : ℝ) (217782174157/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 1 (297429075379/500000000000 : ℝ) (594858150761/1000000000000 : ℝ) (217782174153/500000000000 : ℝ) (217782174157/500000000000 : ℝ) (128802812383/250000000000 : ℝ) (257605624769/500000000000 : ℝ) (254508842071/500000000000 : ℝ) (509017684149/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 2 (128802812383/250000000000 : ℝ) (257605624769/500000000000 : ℝ) (254508842071/500000000000 : ℝ) (509017684149/1000000000000 : ℝ) (512114466837/1000000000000 : ℝ) (128028616711/250000000000 : ℝ) (128026275887/250000000000 : ℝ) (128026275889/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 3 (512114466837/1000000000000 : ℝ) (128028616711/250000000000 : ℝ) (128026275887/250000000000 : ℝ) (128026275889/250000000000 : ℝ) (64013723149/125000000000 : ℝ) (1280274463/2500000000 : ℝ) (512109785171/1000000000000 : ℝ) (512109785179/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 4 (64013723149/125000000000 : ℝ) (1280274463/2500000000 : ℝ) (512109785171/1000000000000 : ℝ) (512109785179/1000000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 5 (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 6 (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1051/8192 : ℝ))) 7 (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1051/8192 : ℝ)) hmem 8 (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1051/8192 : ℝ))) hcmem 8 (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1051/8192 : ℝ)) (12683503/12800000 : ℝ) (990898671877/1000000000000 : ℝ) (512109785181/1000000000000 : ℝ) (51210978519/100000000000 : ℝ) (202952176723/250000000000 : ℝ) (811808706909/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0063_exp_lower
  have heNumeric : (2019115375023/1000000000000 : ℝ)/4 ≤ Real.exp (-10681794981/15625000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019115375023/1000000000000 : ℝ)/4 ≤ Real.exp ((525/4096 : ℝ)-(811808706909/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (525/4096 : ℝ) (1051/8192 : ℝ) (811808706909/1000000000000 : ℝ) (2019115375023/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0064; no trusted numerical premise.
theorem cover7_leaf0064_exp_radius : (498854724655308377/500000000000000000 : ℝ) ≤ Real.exp ((-263/14336 : ℝ)/8) ∧ Real.exp ((-263/14336 : ℝ)/8) ≤ (199541889862123351/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-263/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0064_exp_lower : (918094475450215659/1000000000000000000 : ℝ) ≤ Real.exp ((-1367279667571/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367279667571/2000000000000 : ℝ)/8) ≤ (45904723772510783/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367279667571/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0064_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252388171291/125000000000 : ℝ) ≤ 4*Real.exp (1051/8192 : ℝ)*Real.exp (-mu (radius 7 (263/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (252388171291/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (263/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0064_exp_radius
  have hrNumeric : (61363864303/62500000000 : ℝ) ≤ Real.exp (-263/14336 : ℝ) ∧ Real.exp (-263/14336 : ℝ) ≤ (981821828849/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61363864303/62500000000 : ℝ) ≤ (radius 7 (263/2048 : ℝ)) ∧ (radius 7 (263/2048 : ℝ)) ≤ (981821828849/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (263/2048 : ℝ)) (61363864303/62500000000 : ℝ) (981821828849/1000000000000 : ℝ) (5931402823/31250000000 : ℝ) (94902445171/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (263/2048 : ℝ)) (61363864303/62500000000 : ℝ) (981821828849/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (263/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61363864303/62500000000 : ℝ) (981821828849/1000000000000 : ℝ) (123863864303/125000000000 : ℝ) (39636436577/40000000000 : ℝ) (990869228933/1000000000000 : ℝ) (198173845787/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (263/2048 : ℝ)) 1 (123863864303/125000000000 : ℝ) (39636436577/40000000000 : ℝ) (990869228933/1000000000000 : ℝ) (198173845787/200000000000 : ℝ) (495445035839/500000000000 : ℝ) (1548265737/1562500000 : ℝ) (990890071459/1000000000000 : ℝ) (990890071461/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (263/2048 : ℝ)) 2 (495445035839/500000000000 : ℝ) (1548265737/1562500000 : ℝ) (990890071459/1000000000000 : ℝ) (990890071461/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (263/2048 : ℝ)) 3 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (263/2048 : ℝ)) 4 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (263/2048 : ℝ)) 5 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (263/2048 : ℝ)) 6 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (263/2048 : ℝ)) 7 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (263/2048 : ℝ))) (5931402823/31250000000 : ℝ) (94902445171/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5931402823/31250000000 : ℝ) (94902445171/500000000000 : ℝ) (37181402823/62500000000 : ℝ) (594902445171/1000000000000 : ℝ) (217833015367/500000000000 : ℝ) (217833015371/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 1 (37181402823/62500000000 : ℝ) (594902445171/1000000000000 : ℝ) (217833015367/500000000000 : ℝ) (217833015371/500000000000 : ℝ) (515284237951/1000000000000 : ℝ) (515284237957/1000000000000 : ℝ) (101819209771/200000000000 : ℝ) (254548024431/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 2 (515284237951/1000000000000 : ℝ) (515284237957/1000000000000 : ℝ) (101819209771/200000000000 : ℝ) (254548024431/500000000000 : ℝ) (512190143403/1000000000000 : ℝ) (51219014341/100000000000 : ℝ) (32011299859/62500000000 : ℝ) (512180797751/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 3 (512190143403/1000000000000 : ℝ) (51219014341/100000000000 : ℝ) (32011299859/62500000000 : ℝ) (512180797751/1000000000000 : ℝ) (512185470573/1000000000000 : ℝ) (512185470581/1000000000000 : ℝ) (64023183819/125000000000 : ℝ) (3201159191/6250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 4 (512185470573/1000000000000 : ℝ) (512185470581/1000000000000 : ℝ) (64023183819/125000000000 : ℝ) (3201159191/6250000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 5 (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 6 (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (263/2048 : ℝ))) 7 (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (263/2048 : ℝ)) hmem 8 (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (263/2048 : ℝ))) hcmem 8 (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (263/2048 : ℝ)) (61930629473/62500000000 : ℝ) (990890071571/1000000000000 : ℝ) (256092735281/500000000000 : ℝ) (512185470571/1000000000000 : ℝ) (162387146441/200000000000 : ℝ) (811935732223/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0064_exp_lower
  have heNumeric : (252388171291/125000000000 : ℝ)/4 ≤ Real.exp (-1367279667571/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252388171291/125000000000 : ℝ)/4 ≤ Real.exp ((1051/8192 : ℝ)-(811935732223/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1051/8192 : ℝ) (263/2048 : ℝ) (811935732223/1000000000000 : ℝ) (252388171291/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0065; no trusted numerical premise.
theorem cover7_leaf0065_exp_radius : (498853637239491231/500000000000000000 : ℝ) ≤ Real.exp ((-1053/57344 : ℝ)/8) ∧ Real.exp ((-1053/57344 : ℝ)/8) ≤ (997707274478982463/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1053/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0065_exp_lower : (459046958049831419/500000000000000000 : ℝ) ≤ Real.exp ((-3418223539/5000000000 : ℝ)/8) ∧ Real.exp ((-3418223539/5000000000 : ℝ)/8) ≤ (918093916099662839/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3418223539/5000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0065_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504773882301/250000000000 : ℝ) ≤ 4*Real.exp (263/2048 : ℝ)*Real.exp (-mu (radius 7 (1053/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504773882301/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1053/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0065_exp_radius
  have hrNumeric : (981804707383/1000000000000 : ℝ) ≤ Real.exp (-1053/57344 : ℝ) ∧ Real.exp (-1053/57344 : ℝ) ≤ (122725588423/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981804707383/1000000000000 : ℝ) ≤ (radius 7 (1053/8192 : ℝ)) ∧ (radius 7 (1053/8192 : ℝ)) ≤ (122725588423/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1053/8192 : ℝ)) (981804707383/1000000000000 : ℝ) (122725588423/125000000000 : ℝ) (189893434743/1000000000000 : ℝ) (189893434749/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1053/8192 : ℝ)) (981804707383/1000000000000 : ℝ) (122725588423/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981804707383/1000000000000 : ℝ) (122725588423/125000000000 : ℝ) (990902353691/1000000000000 : ℝ) (247725588423/250000000000 : ℝ) (990860589277/1000000000000 : ℝ) (495430294639/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 1 (990902353691/1000000000000 : ℝ) (247725588423/250000000000 : ℝ) (990860589277/1000000000000 : ℝ) (495430294639/500000000000 : ℝ) (247720367871/250000000000 : ℝ) (198176294297/200000000000 : ℝ) (990881471263/1000000000000 : ℝ) (198176294253/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 2 (247720367871/250000000000 : ℝ) (198176294297/200000000000 : ℝ) (990881471263/1000000000000 : ℝ) (198176294253/200000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 3 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 4 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 5 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 6 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1053/8192 : ℝ)) 7 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1053/8192 : ℝ))) (189893434743/1000000000000 : ℝ) (189893434749/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (189893434743/1000000000000 : ℝ) (189893434749/1000000000000 : ℝ) (594946717371/1000000000000 : ℝ) (4759573739/8000000000 : ℝ) (108941909619/250000000000 : ℝ) (435767638483/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 1 (594946717371/1000000000000 : ℝ) (4759573739/8000000000 : ℝ) (108941909619/250000000000 : ℝ) (435767638483/1000000000000 : ℝ) (515357177923/1000000000000 : ℝ) (515357177929/1000000000000 : ℝ) (509174357217/1000000000000 : ℝ) (63646794653/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 2 (515357177923/1000000000000 : ℝ) (515357177929/1000000000000 : ℝ) (509174357217/1000000000000 : ℝ) (63646794653/125000000000 : ℝ) (51226576757/100000000000 : ℝ) (512265767577/1000000000000 : ℝ) (64032054937/125000000000 : ℝ) (32016027469/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 3 (51226576757/100000000000 : ℝ) (512265767577/1000000000000 : ℝ) (64032054937/125000000000 : ℝ) (32016027469/62500000000 : ℝ) (512261103533/1000000000000 : ℝ) (512261103541/1000000000000 : ℝ) (512261103511/1000000000000 : ℝ) (3201631897/6250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 4 (512261103533/1000000000000 : ℝ) (512261103541/1000000000000 : ℝ) (512261103511/1000000000000 : ℝ) (3201631897/6250000000 : ℝ) (256130551761/500000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 5 (256130551761/500000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 6 (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1053/8192 : ℝ))) 7 (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1053/8192 : ℝ)) hmem 8 (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1053/8192 : ℝ))) hcmem 8 (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1053/8192 : ℝ)) (990881471373/1000000000000 : ℝ) (7927051771/8000000000 : ℝ) (512261103521/1000000000000 : ℝ) (512261103531/1000000000000 : ℝ) (812062676531/1000000000000 : ℝ) (16241253531/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0065_exp_lower
  have heNumeric : (504773882301/250000000000 : ℝ)/4 ≤ Real.exp (-3418223539/5000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504773882301/250000000000 : ℝ)/4 ≤ Real.exp ((263/2048 : ℝ)-(16241253531/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (263/2048 : ℝ) (1053/8192 : ℝ) (16241253531/20000000000 : ℝ) (504773882301/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0066; no trusted numerical premise.
theorem cover7_leaf0066_exp_radius : (997705099652088923/1000000000000000000 : ℝ) ≤ Real.exp ((-527/28672 : ℝ)/8) ∧ Real.exp ((-527/28672 : ℝ)/8) ≤ (249426274913022231/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-527/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0066_exp_lower : (918093366029079451/1000000000000000000 : ℝ) ≤ Real.exp ((-1367299001909/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367299001909/2000000000000 : ℝ)/8) ≤ (229523341507269863/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367299001909/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0066_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201908585139/100000000000 : ℝ) ≤ 4*Real.exp (1053/8192 : ℝ)*Real.exp (-mu (radius 7 (527/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (201908585139/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (527/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0066_exp_radius
  have hrNumeric : (981787586217/1000000000000 : ℝ) ≤ Real.exp (-527/28672 : ℝ) ∧ Real.exp (-527/28672 : ℝ) ≤ (490893793109/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981787586217/1000000000000 : ℝ) ≤ (radius 7 (527/4096 : ℝ)) ∧ (radius 7 (527/4096 : ℝ)) ≤ (490893793109/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (527/4096 : ℝ)) (981787586217/1000000000000 : ℝ) (490893793109/500000000000 : ℝ) (94990967397/500000000000 : ℝ) (474954837/2500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (527/4096 : ℝ)) (981787586217/1000000000000 : ℝ) (490893793109/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (527/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981787586217/1000000000000 : ℝ) (490893793109/500000000000 : ℝ) (247723448277/250000000000 : ℝ) (990893793109/1000000000000 : ℝ) (7741030857/7812500000 : ℝ) (990851949697/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (527/4096 : ℝ)) 1 (247723448277/250000000000 : ℝ) (990893793109/1000000000000 : ℝ) (7741030857/7812500000 : ℝ) (990851949697/1000000000000 : ℝ) (495436435701/500000000000 : ℝ) (990872871403/1000000000000 : ℝ) (990872871181/1000000000000 : ℝ) (990872871183/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (527/4096 : ℝ)) 2 (495436435701/500000000000 : ℝ) (990872871403/1000000000000 : ℝ) (990872871181/1000000000000 : ℝ) (990872871183/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (527/4096 : ℝ)) 3 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (527/4096 : ℝ)) 4 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (527/4096 : ℝ)) 5 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (527/4096 : ℝ)) 6 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (527/4096 : ℝ)) 7 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (527/4096 : ℝ))) (94990967397/500000000000 : ℝ) (474954837/2500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94990967397/500000000000 : ℝ) (474954837/2500000000 : ℝ) (594990967397/1000000000000 : ℝ) (2974954837/5000000000 : ℝ) (435869171649/1000000000000 : ℝ) (54483646457/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 1 (594990967397/1000000000000 : ℝ) (2974954837/5000000000 : ℝ) (435869171649/1000000000000 : ℝ) (54483646457/125000000000 : ℝ) (515430069523/1000000000000 : ℝ) (64428758691/125000000000 : ℝ) (254626304659/500000000000 : ℝ) (20370104373/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 2 (515430069523/1000000000000 : ℝ) (64428758691/125000000000 : ℝ) (254626304659/500000000000 : ℝ) (20370104373/40000000000 : ℝ) (25617066971/50000000000 : ℝ) (512341339427/1000000000000 : ℝ) (512332028889/1000000000000 : ℝ) (16010375903/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 3 (25617066971/50000000000 : ℝ) (512341339427/1000000000000 : ℝ) (512332028889/1000000000000 : ℝ) (16010375903/31250000000 : ℝ) (256168342077/500000000000 : ℝ) (256168342081/500000000000 : ℝ) (512336684133/1000000000000 : ℝ) (512336684141/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 4 (256168342077/500000000000 : ℝ) (256168342081/500000000000 : ℝ) (512336684133/1000000000000 : ℝ) (512336684141/1000000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 5 (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 6 (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (527/4096 : ℝ))) 7 (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (527/4096 : ℝ)) hmem 8 (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (527/4096 : ℝ))) hcmem 8 (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (527/4096 : ℝ)) (990872871291/1000000000000 : ℝ) (990872871293/1000000000000 : ℝ) (512336684143/1000000000000 : ℝ) (64042085519/125000000000 : ℝ) (40609477/50000000 : ℝ) (812189540017/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0066_exp_lower
  have heNumeric : (201908585139/100000000000 : ℝ)/4 ≤ Real.exp (-1367299001909/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201908585139/100000000000 : ℝ)/4 ≤ Real.exp ((1053/8192 : ℝ)-(812189540017/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1053/8192 : ℝ) (527/4096 : ℝ) (812189540017/1000000000000 : ℝ) (201908585139/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0067; no trusted numerical premise.
theorem cover7_leaf0067_exp_radius : (249425731207484031/250000000000000000 : ℝ) ≤ Real.exp ((-1055/57344 : ℝ)/8) ∧ Real.exp ((-1055/57344 : ℝ)/8) ≤ (7981623398639489/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1055/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0067_exp_lower : (183618565044591201/200000000000000000 : ℝ) ≤ Real.exp ((-85456776673/125000000000 : ℝ)/8) ∧ Real.exp ((-85456776673/125000000000 : ℝ)/8) ≤ (459046412611478003/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85456776673/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0067_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019076336613/1000000000000 : ℝ) ≤ 4*Real.exp (527/4096 : ℝ)*Real.exp (-mu (radius 7 (1055/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019076336613/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1055/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0067_exp_radius
  have hrNumeric : (19635409307/20000000000 : ℝ) ≤ Real.exp (-1055/57344 : ℝ) ∧ Real.exp (-1055/57344 : ℝ) ≤ (981770465351/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19635409307/20000000000 : ℝ) ≤ (radius 7 (1055/8192 : ℝ)) ∧ (radius 7 (1055/8192 : ℝ)) ≤ (981770465351/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1055/8192 : ℝ)) (19635409307/20000000000 : ℝ) (981770465351/1000000000000 : ℝ) (190070390551/1000000000000 : ℝ) (190070390557/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1055/8192 : ℝ)) (19635409307/20000000000 : ℝ) (981770465351/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19635409307/20000000000 : ℝ) (981770465351/1000000000000 : ℝ) (39635409307/40000000000 : ℝ) (247721308169/250000000000 : ℝ) (99084331019/100000000000 : ℝ) (61927706887/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 1 (39635409307/40000000000 : ℝ) (247721308169/250000000000 : ℝ) (99084331019/100000000000 : ℝ) (61927706887/62500000000 : ℝ) (123858033929/125000000000 : ℝ) (495432135717/500000000000 : ℝ) (99086427121/100000000000 : ℝ) (990864271213/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 2 (123858033929/125000000000 : ℝ) (495432135717/500000000000 : ℝ) (99086427121/100000000000 : ℝ) (990864271213/1000000000000 : ℝ) (990864271321/1000000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 3 (990864271321/1000000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 4 (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 5 (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 6 (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1055/8192 : ℝ)) 7 (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1055/8192 : ℝ))) (190070390551/1000000000000 : ℝ) (190070390557/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (190070390551/1000000000000 : ℝ) (190070390557/1000000000000 : ℝ) (23801407811/40000000000 : ℝ) (595035195279/1000000000000 : ℝ) (54496328797/125000000000 : ℝ) (27248164399/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 1 (23801407811/40000000000 : ℝ) (595035195279/1000000000000 : ℝ) (54496328797/125000000000 : ℝ) (27248164399/62500000000 : ℝ) (20620116513/40000000000 : ℝ) (8054733013/15625000000 : ℝ) (509330805253/1000000000000 : ℝ) (25466540263/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 2 (20620116513/40000000000 : ℝ) (8054733013/15625000000 : ℝ) (509330805253/1000000000000 : ℝ) (25466540263/50000000000 : ℝ) (512416859039/1000000000000 : ℝ) (256208429523/500000000000 : ℝ) (102481513201/200000000000 : ℝ) (512407566013/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 3 (512416859039/1000000000000 : ℝ) (256208429523/500000000000 : ℝ) (102481513201/200000000000 : ℝ) (512407566013/1000000000000 : ℝ) (256206106261/500000000000 : ℝ) (51241221253/100000000000 : ℝ) (40992977/80000000 : ℝ) (512412212509/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 4 (256206106261/500000000000 : ℝ) (51241221253/100000000000 : ℝ) (40992977/80000000 : ℝ) (512412212509/1000000000000 : ℝ) (512412212511/1000000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 5 (512412212511/1000000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 6 (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1055/8192 : ℝ))) 7 (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1055/8192 : ℝ)) hmem 8 (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1055/8192 : ℝ))) hcmem 8 (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1055/8192 : ℝ)) (24771606783/25000000000 : ℝ) (247716067831/250000000000 : ℝ) (51241221251/100000000000 : ℝ) (12810305313/25000000000 : ℝ) (812316322739/1000000000000 : ℝ) (812316322759/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0067_exp_lower
  have heNumeric : (2019076336613/1000000000000 : ℝ)/4 ≤ Real.exp (-85456776673/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019076336613/1000000000000 : ℝ)/4 ≤ Real.exp ((527/4096 : ℝ)-(812316322759/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (527/4096 : ℝ) (1055/8192 : ℝ) (812316322759/1000000000000 : ℝ) (2019076336613/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0068; no trusted numerical premise.
theorem cover7_leaf0068_exp_radius : (997700750012524057/1000000000000000000 : ℝ) ≤ Real.exp ((-33/1792 : ℝ)/8) ∧ Real.exp ((-33/1792 : ℝ)/8) ≤ (498850375006262029/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0068_exp_lower : (57380768354082767/62500000000000000 : ℝ) ≤ Real.exp ((-273463538091/400000000000 : ℝ)/8) ∧ Real.exp ((-273463538091/400000000000 : ℝ)/8) ≤ (918092293665324273/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273463538091/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0068_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019066984589/1000000000000 : ℝ) ≤ 4*Real.exp (1055/8192 : ℝ)*Real.exp (-mu (radius 7 (33/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019066984589/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (33/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0068_exp_radius
  have hrNumeric : (981753344781/1000000000000 : ℝ) ≤ Real.exp (-33/1792 : ℝ) ∧ Real.exp (-33/1792 : ℝ) ≤ (490876672391/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981753344781/1000000000000 : ℝ) ≤ (radius 7 (33/256 : ℝ)) ∧ (radius 7 (33/256 : ℝ)) ≤ (490876672391/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (33/256 : ℝ)) (981753344781/1000000000000 : ℝ) (490876672391/500000000000 : ℝ) (95079401041/500000000000 : ℝ) (23769850261/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (33/256 : ℝ)) (981753344781/1000000000000 : ℝ) (490876672391/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (33/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981753344781/1000000000000 : ℝ) (490876672391/500000000000 : ℝ) (99087667239/100000000000 : ℝ) (990876672391/1000000000000 : ℝ) (24770866769/25000000000 : ℝ) (990834670761/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (33/256 : ℝ)) 1 (99087667239/100000000000 : ℝ) (990876672391/1000000000000 : ℝ) (24770866769/25000000000 : ℝ) (990834670761/1000000000000 : ℝ) (39634226863/40000000000 : ℝ) (123856958947/125000000000 : ℝ) (123856958919/125000000000 : ℝ) (495427835677/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (33/256 : ℝ)) 2 (39634226863/40000000000 : ℝ) (123856958947/125000000000 : ℝ) (123856958919/125000000000 : ℝ) (495427835677/500000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (33/256 : ℝ)) 3 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (33/256 : ℝ)) 4 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (33/256 : ℝ)) 5 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (33/256 : ℝ)) 6 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (33/256 : ℝ)) 7 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (33/256 : ℝ))) (95079401041/500000000000 : ℝ) (23769850261/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95079401041/500000000000 : ℝ) (23769850261/125000000000 : ℝ) (595079401041/1000000000000 : ℝ) (148769850261/250000000000 : ℝ) (109018003697/250000000000 : ℝ) (109018003699/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 1 (595079401041/1000000000000 : ℝ) (148769850261/250000000000 : ℝ) (109018003697/250000000000 : ℝ) (109018003699/250000000000 : ℝ) (257787853957/500000000000 : ℝ) (6444696349/12500000000 : ℝ) (254704472561/500000000000 : ℝ) (509408945129/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 2 (257787853957/500000000000 : ℝ) (6444696349/12500000000 : ℝ) (254704472561/500000000000 : ℝ) (509408945129/1000000000000 : ℝ) (256246163259/500000000000 : ℝ) (20499693061/40000000000 : ℝ) (256241525469/500000000000 : ℝ) (102496610189/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 3 (256246163259/500000000000 : ℝ) (20499693061/40000000000 : ℝ) (256241525469/500000000000 : ℝ) (102496610189/200000000000 : ℝ) (64060961091/125000000000 : ℝ) (102497537747/200000000000 : ℝ) (512487688707/1000000000000 : ℝ) (102497537743/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 4 (64060961091/125000000000 : ℝ) (102497537747/200000000000 : ℝ) (512487688707/1000000000000 : ℝ) (102497537743/200000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 5 (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 6 (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (33/256 : ℝ))) 7 (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (33/256 : ℝ)) hmem 8 (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (33/256 : ℝ))) hcmem 8 (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (33/256 : ℝ)) (990855671463/1000000000000 : ℝ) (198171134293/200000000000 : ℝ) (512487688717/1000000000000 : ℝ) (20499507549/40000000000 : ℝ) (812443024899/1000000000000 : ℝ) (162488604983/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0068_exp_lower
  have heNumeric : (2019066984589/1000000000000 : ℝ)/4 ≤ Real.exp (-273463538091/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019066984589/1000000000000 : ℝ)/4 ≤ Real.exp ((1055/8192 : ℝ)-(162488604983/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1055/8192 : ℝ) (33/256 : ℝ) (162488604983/200000000000 : ℝ) (2019066984589/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0069; no trusted numerical premise.
theorem cover7_leaf0069_exp_radius : (99769857519985271/100000000000000000 : ℝ) ≤ Real.exp ((-151/8192 : ℝ)/8) ∧ Real.exp ((-151/8192 : ℝ)/8) ≤ (997698575199852711/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-151/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0069_exp_lower : (459045885670567219/500000000000000000 : ℝ) ≤ Real.exp ((-85457924577/125000000000 : ℝ)/8) ∧ Real.exp ((-85457924577/125000000000 : ℝ)/8) ≤ (918091771341134439/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85457924577/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0069_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019057795051/1000000000000 : ℝ) ≤ 4*Real.exp (33/256 : ℝ)*Real.exp (-mu (radius 7 (1057/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019057795051/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1057/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0069_exp_radius
  have hrNumeric : (981736224511/1000000000000 : ℝ) ≤ Real.exp (-151/8192 : ℝ) ∧ Real.exp (-151/8192 : ℝ) ≤ (3834907127/3906250000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981736224511/1000000000000 : ℝ) ≤ (radius 7 (1057/8192 : ℝ)) ∧ (radius 7 (1057/8192 : ℝ)) ≤ (3834907127/3906250000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1057/8192 : ℝ)) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1057/8192 : ℝ)) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981736224511/1000000000000 : ℝ) (3834907127/3906250000 : ℝ) (198173622451/200000000000 : ℝ) (7741157127/7812500000 : ℝ) (198165206281/200000000000 : ℝ) (990826031407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 1 (198173622451/200000000000 : ℝ) (7741157127/7812500000 : ℝ) (198165206281/200000000000 : ℝ) (990826031407/1000000000000 : ℝ) (99084707183/100000000000 : ℝ) (123855883979/125000000000 : ℝ) (495423535803/500000000000 : ℝ) (990847071609/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 2 (99084707183/100000000000 : ℝ) (123855883979/125000000000 : ℝ) (495423535803/500000000000 : ℝ) (990847071609/1000000000000 : ℝ) (495423535859/500000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 3 (495423535859/500000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 4 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 5 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 6 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1057/8192 : ℝ)) 7 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1057/8192 : ℝ))) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95123584721/500000000000 : ℝ) (23780896181/125000000000 : ℝ) (595123584721/1000000000000 : ℝ) (148780896181/250000000000 : ℝ) (17446933/40000000 : ℝ) (27260832813/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 1 (595123584721/1000000000000 : ℝ) (148780896181/250000000000 : ℝ) (17446933/40000000 : ℝ) (27260832813/62500000000 : ℝ) (25782422743/50000000000 : ℝ) (257824227433/500000000000 : ℝ) (254743514507/500000000000 : ℝ) (509487029021/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 2 (25782422743/50000000000 : ℝ) (257824227433/500000000000 : ℝ) (254743514507/500000000000 : ℝ) (509487029021/1000000000000 : ℝ) (512567741937/1000000000000 : ℝ) (64070967743/125000000000 : ℝ) (512558483767/1000000000000 : ℝ) (20502339351/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 3 (512567741937/1000000000000 : ℝ) (64070967743/125000000000 : ℝ) (512558483767/1000000000000 : ℝ) (20502339351/40000000000 : ℝ) (128140778213/250000000000 : ℝ) (25628155643/50000000000 : ℝ) (512563112831/1000000000000 : ℝ) (512563112839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 4 (128140778213/250000000000 : ℝ) (25628155643/50000000000 : ℝ) (512563112831/1000000000000 : ℝ) (512563112839/1000000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 5 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 6 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1057/8192 : ℝ))) 7 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1057/8192 : ℝ)) hmem 8 (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1057/8192 : ℝ))) hcmem 8 (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1057/8192 : ℝ)) (990847071717/1000000000000 : ℝ) (990847071721/1000000000000 : ℝ) (512563112841/1000000000000 : ℝ) (10251262257/20000000000 : ℝ) (406284823299/500000000000 : ℝ) (101571205827/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0069_exp_lower
  have heNumeric : (2019057795051/1000000000000 : ℝ)/4 ≤ Real.exp (-85457924577/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019057795051/1000000000000 : ℝ)/4 ≤ Real.exp ((33/256 : ℝ)-(101571205827/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (33/256 : ℝ) (1057/8192 : ℝ) (101571205827/125000000000 : ℝ) (2019057795051/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0070; no trusted numerical premise.
theorem cover7_leaf0070_exp_radius : (997696400391922073/1000000000000000000 : ℝ) ≤ Real.exp ((-529/28672 : ℝ)/8) ∧ Real.exp ((-529/28672 : ℝ)/8) ≤ (498848200195961037/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-529/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0070_exp_lower : (448286747184999/488281250000000 : ℝ) ≤ Real.exp ((-1367335735369/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367335735369/2000000000000 : ℝ)/8) ≤ (918091258234877953/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367335735369/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0070_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009524383863/500000000000 : ℝ) ≤ 4*Real.exp (1057/8192 : ℝ)*Real.exp (-mu (radius 7 (529/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009524383863/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (529/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0070_exp_radius
  have hrNumeric : (981719104539/1000000000000 : ℝ) ≤ Real.exp (-529/28672 : ℝ) ∧ Real.exp (-529/28672 : ℝ) ≤ (49085955227/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981719104539/1000000000000 : ℝ) ≤ (radius 7 (529/4096 : ℝ)) ∧ (radius 7 (529/4096 : ℝ)) ≤ (49085955227/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (529/4096 : ℝ)) (981719104539/1000000000000 : ℝ) (49085955227/50000000000 : ℝ) (190335492699/1000000000000 : ℝ) (38067098541/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (529/4096 : ℝ)) (981719104539/1000000000000 : ℝ) (49085955227/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (529/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981719104539/1000000000000 : ℝ) (49085955227/50000000000 : ℝ) (990859552269/1000000000000 : ℝ) (99085955227/100000000000 : ℝ) (7926539137/8000000000 : ℝ) (990817392127/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (529/4096 : ℝ)) 1 (990859552269/1000000000000 : ℝ) (99085955227/100000000000 : ℝ) (7926539137/8000000000 : ℝ) (990817392127/1000000000000 : ℝ) (990838472197/1000000000000 : ℝ) (990838472199/1000000000000 : ℝ) (247709617993/250000000000 : ℝ) (39633538879/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (529/4096 : ℝ)) 2 (990838472197/1000000000000 : ℝ) (990838472199/1000000000000 : ℝ) (247709617993/250000000000 : ℝ) (39633538879/40000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (529/4096 : ℝ)) 3 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (529/4096 : ℝ)) 4 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (529/4096 : ℝ)) 5 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (529/4096 : ℝ)) 6 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (529/4096 : ℝ)) 7 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (529/4096 : ℝ))) (190335492699/1000000000000 : ℝ) (38067098541/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (190335492699/1000000000000 : ℝ) (38067098541/200000000000 : ℝ) (595167746349/1000000000000 : ℝ) (595167746353/1000000000000 : ℝ) (436274561141/1000000000000 : ℝ) (436274561149/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 1 (595167746349/1000000000000 : ℝ) (595167746353/1000000000000 : ℝ) (436274561141/1000000000000 : ℝ) (436274561149/1000000000000 : ℝ) (103144230749/200000000000 : ℝ) (515721153751/1000000000000 : ℝ) (509565057027/1000000000000 : ℝ) (101913011407/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 2 (103144230749/200000000000 : ℝ) (515721153751/1000000000000 : ℝ) (509565057027/1000000000000 : ℝ) (101913011407/200000000000 : ℝ) (256321552693/500000000000 : ℝ) (512643105393/1000000000000 : ℝ) (512633864583/1000000000000 : ℝ) (512633864591/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 3 (256321552693/500000000000 : ℝ) (512643105393/1000000000000 : ℝ) (512633864583/1000000000000 : ℝ) (512633864591/1000000000000 : ℝ) (64079810623/125000000000 : ℝ) (1001247041/1953125000 : ℝ) (512638484963/1000000000000 : ℝ) (128159621243/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 4 (64079810623/125000000000 : ℝ) (1001247041/1953125000 : ℝ) (512638484963/1000000000000 : ℝ) (128159621243/250000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 5 (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 6 (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (529/4096 : ℝ))) 7 (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (529/4096 : ℝ)) hmem 8 (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (529/4096 : ℝ))) hcmem 8 (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (529/4096 : ℝ)) (247709618021/250000000000 : ℝ) (990838472087/1000000000000 : ℝ) (512638484973/1000000000000 : ℝ) (256319242491/500000000000 : ℝ) (40634809399/50000000000 : ℝ) (812696187997/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0070_exp_lower
  have heNumeric : (1009524383863/500000000000 : ℝ)/4 ≤ Real.exp (-1367335735369/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009524383863/500000000000 : ℝ)/4 ≤ Real.exp ((1057/8192 : ℝ)-(812696187997/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1057/8192 : ℝ) (529/4096 : ℝ) (812696187997/1000000000000 : ℝ) (1009524383863/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0071; no trusted numerical premise.
theorem cover7_leaf0071_exp_radius : (124711778198591517/125000000000000000 : ℝ) ≤ Real.exp ((-1059/57344 : ℝ)/8) ∧ Real.exp ((-1059/57344 : ℝ)/8) ≤ (997694225588732137/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1059/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0071_exp_lower : (28690336072838033/31250000000000000 : ℝ) ≤ Real.exp ((-68367225857/100000000000 : ℝ)/8) ∧ Real.exp ((-68367225857/100000000000 : ℝ)/8) ≤ (918090754330817057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68367225857/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0071_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019039902333/1000000000000 : ℝ) ≤ 4*Real.exp (529/4096 : ℝ)*Real.exp (-mu (radius 7 (1059/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019039902333/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1059/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0071_exp_radius
  have hrNumeric : (196340396973/200000000000 : ℝ) ≤ Real.exp (-1059/57344 : ℝ) ∧ Real.exp (-1059/57344 : ℝ) ≤ (490850992433/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196340396973/200000000000 : ℝ) ≤ (radius 7 (1059/8192 : ℝ)) ∧ (radius 7 (1059/8192 : ℝ)) ≤ (490850992433/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1059/8192 : ℝ)) (196340396973/200000000000 : ℝ) (490850992433/500000000000 : ℝ) (95211885957/500000000000 : ℝ) (2380297149/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1059/8192 : ℝ)) (196340396973/200000000000 : ℝ) (490850992433/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196340396973/200000000000 : ℝ) (490850992433/500000000000 : ℝ) (61928187027/62500000000 : ℝ) (990850992433/1000000000000 : ℝ) (990808752921/1000000000000 : ℝ) (495404376461/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 1 (61928187027/62500000000 : ℝ) (990850992433/1000000000000 : ℝ) (990808752921/1000000000000 : ℝ) (495404376461/500000000000 : ℝ) (247707468169/250000000000 : ℝ) (495414936339/500000000000 : ℝ) (990829872451/1000000000000 : ℝ) (990829872453/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 2 (247707468169/250000000000 : ℝ) (495414936339/500000000000 : ℝ) (990829872451/1000000000000 : ℝ) (990829872453/1000000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 3 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 4 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 5 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 6 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1059/8192 : ℝ)) 7 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1059/8192 : ℝ))) (95211885957/500000000000 : ℝ) (2380297149/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95211885957/500000000000 : ℝ) (2380297149/12500000000 : ℝ) (595211885957/1000000000000 : ℝ) (14880297149/25000000000 : ℝ) (109093930833/250000000000 : ℝ) (21818786167/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 1 (595211885957/1000000000000 : ℝ) (14880297149/25000000000 : ℝ) (109093930833/250000000000 : ℝ) (21818786167/50000000000 : ℝ) (128948451161/250000000000 : ℝ) (10315876093/20000000000 : ℝ) (509643029257/1000000000000 : ℝ) (509643029263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 2 (128948451161/250000000000 : ℝ) (10315876093/20000000000 : ℝ) (509643029257/1000000000000 : ℝ) (509643029263/1000000000000 : ℝ) (10254368339/20000000000 : ℝ) (512718416957/1000000000000 : ℝ) (2002770287/3906250000 : ℝ) (512709193479/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 3 (10254368339/20000000000 : ℝ) (512718416957/1000000000000 : ℝ) (2002770287/3906250000 : ℝ) (512709193479/1000000000000 : ℝ) (512713805211/1000000000000 : ℝ) (256356902609/500000000000 : ℝ) (51271380519/100000000000 : ℝ) (256356902599/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 4 (512713805211/1000000000000 : ℝ) (256356902609/500000000000 : ℝ) (51271380519/100000000000 : ℝ) (256356902599/500000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 5 (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 6 (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1059/8192 : ℝ))) 7 (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1059/8192 : ℝ)) hmem 8 (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1059/8192 : ℝ))) hcmem 8 (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1059/8192 : ℝ)) (990829872563/1000000000000 : ℝ) (495414936283/500000000000 : ℝ) (1281784513/2500000000 : ℝ) (64089225651/125000000000 : ℝ) (812822649179/1000000000000 : ℝ) (162564529839/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0071_exp_lower
  have heNumeric : (2019039902333/1000000000000 : ℝ)/4 ≤ Real.exp (-68367225857/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019039902333/1000000000000 : ℝ)/4 ≤ Real.exp ((529/4096 : ℝ)-(162564529839/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (529/4096 : ℝ) (1059/8192 : ℝ) (162564529839/200000000000 : ℝ) (2019039902333/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0072; no trusted numerical premise.
theorem cover7_leaf0072_exp_radius : (997692050790282889/1000000000000000000 : ℝ) ≤ Real.exp ((-265/14336 : ℝ)/8) ∧ Real.exp ((-265/14336 : ℝ)/8) ≤ (99769205079028289/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-265/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0072_exp_lower : (114761282451938691/125000000000000000 : ℝ) ≤ Real.exp ((-1367353138779/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367353138779/2000000000000 : ℝ)/8) ≤ (918090259615509529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367353138779/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0072_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504757799659/250000000000 : ℝ) ≤ 4*Real.exp (1059/8192 : ℝ)*Real.exp (-mu (radius 7 (265/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (504757799659/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (265/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0072_exp_radius
  have hrNumeric : (981684865491/1000000000000 : ℝ) ≤ Real.exp (-265/14336 : ℝ) ∧ Real.exp (-265/14336 : ℝ) ≤ (245421216373/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981684865491/1000000000000 : ℝ) ≤ (radius 7 (265/2048 : ℝ)) ∧ (radius 7 (265/2048 : ℝ)) ≤ (245421216373/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (265/2048 : ℝ)) (981684865491/1000000000000 : ℝ) (245421216373/250000000000 : ℝ) (95256003569/500000000000 : ℝ) (23814000893/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (265/2048 : ℝ)) (981684865491/1000000000000 : ℝ) (245421216373/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (265/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981684865491/1000000000000 : ℝ) (245421216373/250000000000 : ℝ) (198168486549/200000000000 : ℝ) (495421216373/500000000000 : ℝ) (7740625889/7812500000 : ℝ) (990800113793/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (265/2048 : ℝ)) 1 (198168486549/200000000000 : ℝ) (495421216373/500000000000 : ℝ) (7740625889/7812500000 : ℝ) (990800113793/1000000000000 : ℝ) (247705318317/250000000000 : ℝ) (99082127327/100000000000 : ℝ) (495410636521/500000000000 : ℝ) (247705318261/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (265/2048 : ℝ)) 2 (247705318317/250000000000 : ℝ) (99082127327/100000000000 : ℝ) (495410636521/500000000000 : ℝ) (247705318261/250000000000 : ℝ) (198164254631/200000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (265/2048 : ℝ)) 3 (198164254631/200000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (265/2048 : ℝ)) 4 (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (265/2048 : ℝ)) 5 (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (265/2048 : ℝ)) 6 (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (265/2048 : ℝ)) 7 (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (265/2048 : ℝ))) (95256003569/500000000000 : ℝ) (23814000893/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95256003569/500000000000 : ℝ) (23814000893/125000000000 : ℝ) (595256003569/1000000000000 : ℝ) (148814000893/250000000000 : ℝ) (109119202921/250000000000 : ℝ) (109119202923/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 1 (595256003569/1000000000000 : ℝ) (148814000893/250000000000 : ℝ) (109119202921/250000000000 : ℝ) (109119202923/250000000000 : ℝ) (257933203813/500000000000 : ℝ) (32241650477/62500000000 : ℝ) (254860472893/500000000000 : ℝ) (509720945793/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 2 (257933203813/500000000000 : ℝ) (32241650477/62500000000 : ℝ) (254860472893/500000000000 : ℝ) (509720945793/1000000000000 : ℝ) (256396838353/500000000000 : ℝ) (512793676713/1000000000000 : ℝ) (128196117627/250000000000 : ℝ) (102556894103/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 3 (256396838353/500000000000 : ℝ) (512793676713/1000000000000 : ℝ) (128196117627/250000000000 : ℝ) (102556894103/200000000000 : ℝ) (512789073607/1000000000000 : ℝ) (256394536807/500000000000 : ℝ) (256394536793/500000000000 : ℝ) (256394536797/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 4 (512789073607/1000000000000 : ℝ) (256394536807/500000000000 : ℝ) (256394536793/500000000000 : ℝ) (256394536797/500000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 5 (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 6 (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (265/2048 : ℝ))) 7 (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (265/2048 : ℝ)) hmem 8 (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (265/2048 : ℝ))) hcmem 8 (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (265/2048 : ℝ)) (495410636577/500000000000 : ℝ) (990821273157/1000000000000 : ℝ) (128197268399/250000000000 : ℝ) (128197268401/250000000000 : ℝ) (812949030311/1000000000000 : ℝ) (812949030327/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0072_exp_lower
  have heNumeric : (504757799659/250000000000 : ℝ)/4 ≤ Real.exp (-1367353138779/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504757799659/250000000000 : ℝ)/4 ≤ Real.exp ((1059/8192 : ℝ)-(812949030327/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1059/8192 : ℝ) (265/2048 : ℝ) (812949030327/1000000000000 : ℝ) (504757799659/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0073; no trusted numerical premise.
theorem cover7_leaf0073_exp_radius : (12471123449957179/12500000000000000 : ℝ) ≤ Real.exp ((-1061/57344 : ℝ)/8) ∧ Real.exp ((-1061/57344 : ℝ)/8) ≤ (997689875996574321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1061/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0073_exp_lower : (114761221758937101/125000000000000000 : ℝ) ≤ Real.exp ((-136736160059/200000000000 : ℝ)/8) ∧ Real.exp ((-136736160059/200000000000 : ℝ)/8) ≤ (918089774071496809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136736160059/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0073_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019022656323/1000000000000 : ℝ) ≤ 4*Real.exp (265/2048 : ℝ)*Real.exp (-mu (radius 7 (1061/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019022656323/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1061/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0073_exp_radius
  have hrNumeric : (490833873207/500000000000 : ℝ) ≤ Real.exp (-1061/57344 : ℝ) ∧ Real.exp (-1061/57344 : ℝ) ≤ (196333549283/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490833873207/500000000000 : ℝ) ≤ (radius 7 (1061/8192 : ℝ)) ∧ (radius 7 (1061/8192 : ℝ)) ≤ (196333549283/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1061/8192 : ℝ)) (490833873207/500000000000 : ℝ) (196333549283/200000000000 : ℝ) (11912512403/62500000000 : ℝ) (95300099227/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1061/8192 : ℝ)) (490833873207/500000000000 : ℝ) (196333549283/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490833873207/500000000000 : ℝ) (196333549283/200000000000 : ℝ) (990833873207/1000000000000 : ℝ) (123854234151/125000000000 : ℝ) (495395737369/500000000000 : ℝ) (990791474739/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 1 (990833873207/1000000000000 : ℝ) (123854234151/125000000000 : ℝ) (495395737369/500000000000 : ℝ) (990791474739/1000000000000 : ℝ) (247703168493/250000000000 : ℝ) (495406336987/500000000000 : ℝ) (198162534749/200000000000 : ℝ) (990812673747/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 2 (247703168493/250000000000 : ℝ) (495406336987/500000000000 : ℝ) (198162534749/200000000000 : ℝ) (990812673747/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 3 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 4 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 5 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 6 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1061/8192 : ℝ)) 7 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1061/8192 : ℝ))) (11912512403/62500000000 : ℝ) (95300099227/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11912512403/62500000000 : ℝ) (95300099227/500000000000 : ℝ) (74412512403/125000000000 : ℝ) (595300099227/1000000000000 : ℝ) (87315565267/200000000000 : ℝ) (436577826343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 1 (74412512403/125000000000 : ℝ) (595300099227/1000000000000 : ℝ) (87315565267/200000000000 : ℝ) (436577826343/1000000000000 : ℝ) (515938962779/1000000000000 : ℝ) (103187792557/200000000000 : ℝ) (509798806723/1000000000000 : ℝ) (509798806729/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 2 (515938962779/1000000000000 : ℝ) (103187792557/200000000000 : ℝ) (509798806723/1000000000000 : ℝ) (509798806729/1000000000000 : ℝ) (512868884751/1000000000000 : ℝ) (512868884757/1000000000000 : ℝ) (51285969579/100000000000 : ℝ) (512859695797/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 3 (512868884751/1000000000000 : ℝ) (512868884757/1000000000000 : ℝ) (51285969579/100000000000 : ℝ) (512859695797/1000000000000 : ℝ) (51286429027/100000000000 : ℝ) (512864290277/1000000000000 : ℝ) (512864290249/1000000000000 : ℝ) (512864290257/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 4 (51286429027/100000000000 : ℝ) (512864290277/1000000000000 : ℝ) (512864290249/1000000000000 : ℝ) (512864290257/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 5 (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 6 (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1061/8192 : ℝ))) 7 (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1061/8192 : ℝ)) hmem 8 (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1061/8192 : ℝ))) hcmem 8 (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1061/8192 : ℝ)) (495406336929/500000000000 : ℝ) (990812673861/1000000000000 : ℝ) (512864290259/1000000000000 : ℝ) (512864290267/1000000000000 : ℝ) (813075331529/1000000000000 : ℝ) (162615066309/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0073_exp_lower
  have heNumeric : (2019022656323/1000000000000 : ℝ)/4 ≤ Real.exp (-136736160059/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019022656323/1000000000000 : ℝ)/4 ≤ Real.exp ((265/2048 : ℝ)-(162615066309/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (265/2048 : ℝ) (1061/8192 : ℝ) (162615066309/200000000000 : ℝ) (2019022656323/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0074; no trusted numerical premise.
theorem cover7_leaf0074_exp_radius : (997687701207606421/1000000000000000000 : ℝ) ≤ Real.exp ((-531/28672 : ℝ)/8) ∧ Real.exp ((-531/28672 : ℝ)/8) ≤ (498843850603803211/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-531/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0074_exp_lower : (229522324421391703/250000000000000000 : ℝ) ≤ Real.exp ((-1367369902803/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367369902803/2000000000000 : ℝ)/8) ≤ (918089297685566813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367369902803/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0074_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014275163/1000000000000 : ℝ) ≤ 4*Real.exp (1061/8192 : ℝ)*Real.exp (-mu (radius 7 (531/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014275163/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (531/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0074_exp_radius
  have hrNumeric : (981650627637/1000000000000 : ℝ) ≤ Real.exp (-531/28672 : ℝ) ∧ Real.exp (-531/28672 : ℝ) ≤ (490825313819/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981650627637/1000000000000 : ℝ) ≤ (radius 7 (531/4096 : ℝ)) ∧ (radius 7 (531/4096 : ℝ)) ≤ (490825313819/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (531/4096 : ℝ)) (981650627637/1000000000000 : ℝ) (490825313819/500000000000 : ℝ) (190688345889/1000000000000 : ℝ) (38137669179/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (531/4096 : ℝ)) (981650627637/1000000000000 : ℝ) (490825313819/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (531/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981650627637/1000000000000 : ℝ) (490825313819/500000000000 : ℝ) (495412656909/500000000000 : ℝ) (990825313819/1000000000000 : ℝ) (12384785447/12500000000 : ℝ) (990782835761/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (531/4096 : ℝ)) 1 (495412656909/500000000000 : ℝ) (990825313819/1000000000000 : ℝ) (12384785447/12500000000 : ℝ) (990782835761/1000000000000 : ℝ) (990804074789/1000000000000 : ℝ) (99080407479/100000000000 : ℝ) (990804074561/1000000000000 : ℝ) (990804074563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (531/4096 : ℝ)) 2 (990804074789/1000000000000 : ℝ) (99080407479/100000000000 : ℝ) (990804074561/1000000000000 : ℝ) (990804074563/1000000000000 : ℝ) (39632162987/40000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (531/4096 : ℝ)) 3 (39632162987/40000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (531/4096 : ℝ)) 4 (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (531/4096 : ℝ)) 5 (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (531/4096 : ℝ)) 6 (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (531/4096 : ℝ)) 7 (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (531/4096 : ℝ))) (190688345889/1000000000000 : ℝ) (38137669179/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (190688345889/1000000000000 : ℝ) (38137669179/200000000000 : ℝ) (37209010809/62500000000 : ℝ) (148836043237/250000000000 : ℝ) (436678767389/1000000000000 : ℝ) (436678767397/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 1 (37209010809/62500000000 : ℝ) (148836043237/250000000000 : ℝ) (436678767389/1000000000000 : ℝ) (436678767397/1000000000000 : ℝ) (258005735083/500000000000 : ℝ) (516011470173/1000000000000 : ℝ) (101975322429/200000000000 : ℝ) (509876612153/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 2 (258005735083/500000000000 : ℝ) (516011470173/1000000000000 : ℝ) (101975322429/200000000000 : ℝ) (509876612153/1000000000000 : ℝ) (102588808231/200000000000 : ℝ) (512944041163/1000000000000 : ℝ) (51293486939/100000000000 : ℝ) (256467434699/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 3 (102588808231/200000000000 : ℝ) (512944041163/1000000000000 : ℝ) (51293486939/100000000000 : ℝ) (256467434699/500000000000 : ℝ) (64117431909/125000000000 : ℝ) (512939455281/1000000000000 : ℝ) (128234863813/250000000000 : ℝ) (512939455261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 4 (64117431909/125000000000 : ℝ) (512939455281/1000000000000 : ℝ) (128234863813/250000000000 : ℝ) (512939455261/1000000000000 : ℝ) (256469727631/500000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 5 (256469727631/500000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 6 (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (531/4096 : ℝ))) 7 (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (531/4096 : ℝ)) hmem 8 (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (531/4096 : ℝ))) hcmem 8 (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (531/4096 : ℝ)) (495402037337/500000000000 : ℝ) (990804074677/1000000000000 : ℝ) (512939455261/1000000000000 : ℝ) (512939455271/1000000000000 : ℝ) (162640310589/200000000000 : ℝ) (203300388241/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0074_exp_lower
  have heNumeric : (2019014275163/1000000000000 : ℝ)/4 ≤ Real.exp (-1367369902803/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014275163/1000000000000 : ℝ)/4 ≤ Real.exp ((1061/8192 : ℝ)-(203300388241/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1061/8192 : ℝ) (531/4096 : ℝ) (203300388241/250000000000 : ℝ) (2019014275163/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0050_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0050_certificate
#check SmaleRate.Proofs.cover7_leaf0051_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0051_certificate
#check SmaleRate.Proofs.cover7_leaf0052_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0052_certificate
#check SmaleRate.Proofs.cover7_leaf0053_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0053_certificate
#check SmaleRate.Proofs.cover7_leaf0054_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0054_certificate
#check SmaleRate.Proofs.cover7_leaf0055_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0055_certificate
#check SmaleRate.Proofs.cover7_leaf0056_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0056_certificate
#check SmaleRate.Proofs.cover7_leaf0057_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0057_certificate
#check SmaleRate.Proofs.cover7_leaf0058_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0058_certificate
#check SmaleRate.Proofs.cover7_leaf0059_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0059_certificate
#check SmaleRate.Proofs.cover7_leaf0060_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0060_certificate
#check SmaleRate.Proofs.cover7_leaf0061_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0061_certificate
#check SmaleRate.Proofs.cover7_leaf0062_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0062_certificate
#check SmaleRate.Proofs.cover7_leaf0063_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0063_certificate
#check SmaleRate.Proofs.cover7_leaf0064_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0064_certificate
#check SmaleRate.Proofs.cover7_leaf0065_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0065_certificate
#check SmaleRate.Proofs.cover7_leaf0066_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0066_certificate
#check SmaleRate.Proofs.cover7_leaf0067_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0067_certificate
#check SmaleRate.Proofs.cover7_leaf0068_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0068_certificate
#check SmaleRate.Proofs.cover7_leaf0069_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0069_certificate
#check SmaleRate.Proofs.cover7_leaf0070_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0070_certificate
#check SmaleRate.Proofs.cover7_leaf0071_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0071_certificate
#check SmaleRate.Proofs.cover7_leaf0072_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0072_certificate
#check SmaleRate.Proofs.cover7_leaf0073_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0073_certificate
#check SmaleRate.Proofs.cover7_leaf0074_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0074_certificate
