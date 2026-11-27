/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0000; no trusted numerical premise.
theorem cover7_leaf0000_exp_radius : (499721059979342561/500000000000000000 : ℝ) ≤ Real.exp ((-1/224 : ℝ)/8) ∧ Real.exp ((-1/224 : ℝ)/8) ≤ (999442119958685123/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/224 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0000_exp_lower : (460477294314644249/500000000000000000 : ℝ) ≤ Real.exp ((-658756404271/1000000000000 : ℝ)/8) ∧ Real.exp ((-658756404271/1000000000000 : ℝ)/8) ≤ (920954588629288499/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-658756404271/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0000_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (206997795373/100000000000 : ℝ) ≤ 4*Real.exp (0/1 : ℝ)*Real.exp (-mu (radius 7 (1/32 : ℝ))) ∧ (2019/1000 : ℝ) < (206997795373/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0000_exp_radius
  have hrNumeric : (248886416099/250000000000 : ℝ) ≤ Real.exp (-1/224 : ℝ) ∧ Real.exp (-1/224 : ℝ) ≤ (995545664397/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (248886416099/250000000000 : ℝ) ≤ (radius 7 (1/32 : ℝ)) ∧ (radius 7 (1/32 : ℝ)) ≤ (995545664397/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/32 : ℝ)) (248886416099/250000000000 : ℝ) (995545664397/1000000000000 : ℝ) (92070891/976562500 : ℝ) (18856118479/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/32 : ℝ)) (248886416099/250000000000 : ℝ) (995545664397/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (248886416099/250000000000 : ℝ) (995545664397/1000000000000 : ℝ) (498886416099/500000000000 : ℝ) (997772832199/1000000000000 : ℝ) (24944258663/25000000000 : ℝ) (498885173261/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/32 : ℝ)) 1 (498886416099/500000000000 : ℝ) (997772832199/1000000000000 : ℝ) (24944258663/25000000000 : ℝ) (498885173261/500000000000 : ℝ) (997771589359/1000000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (12472144867/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/32 : ℝ)) 2 (997771589359/1000000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (12472144867/12500000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/32 : ℝ)) 3 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/32 : ℝ)) 4 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/32 : ℝ)) 5 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/32 : ℝ)) 6 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/32 : ℝ)) 7 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/32 : ℝ))) (92070891/976562500 : ℝ) (18856118479/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92070891/976562500 : ℝ) (18856118479/200000000000 : ℝ) (1068633391/1953125000 : ℝ) (273570148099/500000000000 : ℝ) (307051449083/1000000000000 : ℝ) (307051449101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 1 (1068633391/1953125000 : ℝ) (273570148099/500000000000 : ℝ) (307051449083/1000000000000 : ℝ) (307051449101/1000000000000 : ℝ) (427095872637/1000000000000 : ℝ) (8541917453/20000000000 : ℝ) (409878299983/1000000000000 : ℝ) (204939149999/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 2 (427095872637/1000000000000 : ℝ) (8541917453/20000000000 : ℝ) (409878299983/1000000000000 : ℝ) (204939149999/500000000000 : ℝ) (41848708631/100000000000 : ℝ) (104621771581/250000000000 : ℝ) (209199265179/500000000000 : ℝ) (418398530373/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 3 (41848708631/100000000000 : ℝ) (104621771581/250000000000 : ℝ) (209199265179/500000000000 : ℝ) (418398530373/1000000000000 : ℝ) (209221404167/500000000000 : ℝ) (418442808349/1000000000000 : ℝ) (418442805991/1000000000000 : ℝ) (209221403003/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 4 (209221404167/500000000000 : ℝ) (418442808349/1000000000000 : ℝ) (418442805991/1000000000000 : ℝ) (209221403003/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 5 (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 6 (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/32 : ℝ))) 7 (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/32 : ℝ)) hmem 8 (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/32 : ℝ))) hcmem 8 (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/32 : ℝ)) (498885794679/500000000000 : ℝ) (997771589361/1000000000000 : ℝ) (209221403581/500000000000 : ℝ) (209221403589/500000000000 : ℝ) (658756404243/1000000000000 : ℝ) (658756404271/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0000_exp_lower
  have heNumeric : (206997795373/100000000000 : ℝ)/4 ≤ Real.exp (-658756404271/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (206997795373/100000000000 : ℝ)/4 ≤ Real.exp ((0/1 : ℝ)-(658756404271/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (0/1 : ℝ) (1/32 : ℝ) (658756404271/1000000000000 : ℝ) (206997795373/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0001; no trusted numerical premise.
theorem cover7_leaf0001_exp_radius : (499581648330092229/500000000000000000 : ℝ) ≤ Real.exp ((-3/448 : ℝ)/8) ∧ Real.exp ((-3/448 : ℝ)/8) ≤ (999163296660184459/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0001_exp_lower : (460106391979747973/500000000000000000 : ℝ) ≤ Real.exp ((-332601395077/500000000000 : ℝ)/8) ∧ Real.exp ((-332601395077/500000000000 : ℝ)/8) ≤ (920212783959495947/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332601395077/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0001_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056676994689/1000000000000 : ℝ) ≤ 4*Real.exp (1/32 : ℝ)*Real.exp (-mu (radius 7 (3/64 : ℝ))) ∧ (2019/1000 : ℝ) < (2056676994689/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (3/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0001_exp_radius
  have hrNumeric : (993325942543/1000000000000 : ℝ) ≤ Real.exp (-3/448 : ℝ) ∧ Real.exp (-3/448 : ℝ) ≤ (62082871409/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (993325942543/1000000000000 : ℝ) ≤ (radius 7 (3/64 : ℝ)) ∧ (radius 7 (3/64 : ℝ)) ≤ (62082871409/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (3/64 : ℝ)) (993325942543/1000000000000 : ℝ) (62082871409/62500000000 : ℝ) (115341110923/1000000000000 : ℝ) (115341110933/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (3/64 : ℝ)) (993325942543/1000000000000 : ℝ) (62082871409/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (3/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (993325942543/1000000000000 : ℝ) (62082871409/62500000000 : ℝ) (996662971271/1000000000000 : ℝ) (124582871409/125000000000 : ℝ) (996657384733/1000000000000 : ℝ) (498328692367/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (3/64 : ℝ)) 1 (996662971271/1000000000000 : ℝ) (124582871409/125000000000 : ℝ) (996657384733/1000000000000 : ℝ) (498328692367/500000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660178003/1000000000000 : ℝ) (498330088999/500000000000 : ℝ) (498330089/500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (3/64 : ℝ)) 2 (498330089001/500000000000 : ℝ) (996660178003/1000000000000 : ℝ) (498330088999/500000000000 : ℝ) (498330089/500000000 : ℝ) (498330089/500000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (3/64 : ℝ)) 3 (498330089/500000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (3/64 : ℝ)) 4 (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (3/64 : ℝ)) 5 (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (3/64 : ℝ)) 6 (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (3/64 : ℝ)) 7 (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (3/64 : ℝ))) (115341110923/1000000000000 : ℝ) (115341110933/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (115341110923/1000000000000 : ℝ) (115341110933/1000000000000 : ℝ) (557670555461/1000000000000 : ℝ) (557670555467/1000000000000 : ℝ) (84904766843/250000000000 : ℝ) (84904766847/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 1 (557670555461/1000000000000 : ℝ) (557670555467/1000000000000 : ℝ) (84904766843/250000000000 : ℝ) (84904766847/250000000000 : ℝ) (56080601427/125000000000 : ℝ) (112161202857/250000000000 : ℝ) (27199749679/62500000000 : ℝ) (217597997439/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 2 (56080601427/125000000000 : ℝ) (112161202857/250000000000 : ℝ) (27199749679/62500000000 : ℝ) (217597997439/500000000000 : ℝ) (22096020157/50000000000 : ℝ) (441920403153/1000000000000 : ℝ) (220934619879/500000000000 : ℝ) (110467309943/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 3 (22096020157/50000000000 : ℝ) (441920403153/1000000000000 : ℝ) (220934619879/500000000000 : ℝ) (110467309943/250000000000 : ℝ) (441894821449/1000000000000 : ℝ) (441894821463/1000000000000 : ℝ) (110473705177/250000000000 : ℝ) (441894820723/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 4 (441894821449/1000000000000 : ℝ) (441894821463/1000000000000 : ℝ) (110473705177/250000000000 : ℝ) (441894820723/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 5 (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 6 (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (3/64 : ℝ))) 7 (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (3/64 : ℝ)) hmem 8 (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (3/64 : ℝ))) hcmem 8 (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (3/64 : ℝ)) (996660177999/1000000000000 : ℝ) (498330089001/500000000000 : ℝ) (220947410539/500000000000 : ℝ) (441894821093/1000000000000 : ℝ) (43528299383/62500000000 : ℝ) (348226395077/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0001_exp_lower
  have heNumeric : (2056676994689/1000000000000 : ℝ)/4 ≤ Real.exp (-332601395077/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056676994689/1000000000000 : ℝ)/4 ≤ Real.exp ((1/32 : ℝ)-(348226395077/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1/32 : ℝ) (3/64 : ℝ) (348226395077/500000000000 : ℝ) (2056676994689/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0002; no trusted numerical premise.
theorem cover7_leaf0002_exp_radius : (499442275573755371/500000000000000000 : ℝ) ≤ Real.exp ((-1/112 : ℝ)/8) ∧ Real.exp ((-1/112 : ℝ)/8) ≤ (998884551147510743/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/112 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0002_exp_lower : (918621261161350861/1000000000000000000 : ℝ) ≤ Real.exp ((-135810179487/200000000000 : ℝ)/8) ∧ Real.exp ((-135810179487/200000000000 : ℝ)/8) ≤ (459310630580675431/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-135810179487/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0002_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (405678441683/200000000000 : ℝ) ≤ 4*Real.exp (3/64 : ℝ)*Real.exp (-mu (radius 7 (1/16 : ℝ))) ∧ (2019/1000 : ℝ) < (405678441683/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0002_exp_radius
  have hrNumeric : (991111169899/1000000000000 : ℝ) ≤ Real.exp (-1/112 : ℝ) ∧ Real.exp (-1/112 : ℝ) ≤ (9911111699/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (991111169899/1000000000000 : ℝ) ≤ (radius 7 (1/16 : ℝ)) ∧ (radius 7 (1/16 : ℝ)) ≤ (9911111699/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/16 : ℝ)) (991111169899/1000000000000 : ℝ) (9911111699/10000000000 : ℝ) (16629533639/125000000000 : ℝ) (133036269121/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/16 : ℝ)) (991111169899/1000000000000 : ℝ) (9911111699/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (991111169899/1000000000000 : ℝ) (9911111699/10000000000 : ℝ) (995555584949/1000000000000 : ℝ) (19911111699/20000000000 : ℝ) (248886416099/250000000000 : ℝ) (497772832199/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/16 : ℝ)) 1 (995555584949/1000000000000 : ℝ) (19911111699/20000000000 : ℝ) (248886416099/250000000000 : ℝ) (497772832199/500000000000 : ℝ) (31110957021/31250000000 : ℝ) (497775312337/500000000000 : ℝ) (49777531233/50000000000 : ℝ) (497775312331/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/16 : ℝ)) 2 (31110957021/31250000000 : ℝ) (497775312337/500000000000 : ℝ) (49777531233/50000000000 : ℝ) (497775312331/500000000000 : ℝ) (497775312333/500000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/16 : ℝ)) 3 (497775312333/500000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/16 : ℝ)) 4 (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/16 : ℝ)) 5 (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/16 : ℝ)) 6 (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/16 : ℝ)) 7 (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/16 : ℝ))) (16629533639/125000000000 : ℝ) (133036269121/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (16629533639/125000000000 : ℝ) (133036269121/1000000000000 : ℝ) (141629533639/250000000000 : ℝ) (566518134561/1000000000000 : ℝ) (364741372909/1000000000000 : ℝ) (182370686461/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 1 (141629533639/250000000000 : ℝ) (566518134561/1000000000000 : ℝ) (364741372909/1000000000000 : ℝ) (182370686461/500000000000 : ℝ) (116407438433/250000000000 : ℝ) (232814876871/500000000000 : ℝ) (454568589077/1000000000000 : ℝ) (14205268409/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 2 (116407438433/250000000000 : ℝ) (232814876871/500000000000 : ℝ) (454568589077/1000000000000 : ℝ) (14205268409/31250000000 : ℝ) (115024792851/250000000000 : ℝ) (92019834283/200000000000 : ℝ) (23003296513/50000000000 : ℝ) (460065930271/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 3 (115024792851/250000000000 : ℝ) (92019834283/200000000000 : ℝ) (23003296513/50000000000 : ℝ) (460065930271/1000000000000 : ℝ) (28755159427/62500000000 : ℝ) (460082550843/1000000000000 : ℝ) (460082550531/1000000000000 : ℝ) (460082550543/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 4 (28755159427/62500000000 : ℝ) (460082550843/1000000000000 : ℝ) (460082550531/1000000000000 : ℝ) (460082550543/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 5 (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 6 (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/16 : ℝ))) 7 (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/16 : ℝ)) hmem 8 (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/16 : ℝ))) hcmem 8 (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/16 : ℝ)) (199110124933/200000000000 : ℝ) (248887656167/250000000000 : ℝ) (460082550681/1000000000000 : ℝ) (460082550693/1000000000000 : ℝ) (181481474353/250000000000 : ℝ) (145185179487/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0002_exp_lower
  have heNumeric : (405678441683/200000000000 : ℝ)/4 ≤ Real.exp (-135810179487/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (405678441683/200000000000 : ℝ)/4 ≤ Real.exp ((3/64 : ℝ)-(145185179487/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (3/64 : ℝ) (1/16 : ℝ) (145185179487/200000000000 : ℝ) (405678441683/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0003; no trusted numerical premise.
theorem cover7_leaf0003_exp_radius : (998745207554077313/1000000000000000000 : ℝ) ≤ Real.exp ((-9/896 : ℝ)/8) ∧ Real.exp ((-9/896 : ℝ)/8) ≤ (499372603777038657/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0003_exp_lower : (459472892886668297/500000000000000000 : ℝ) ≤ Real.exp ((-67622520797/100000000000 : ℝ)/8) ∧ Real.exp ((-67622520797/100000000000 : ℝ)/8) ≤ (183789157154667319/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67622520797/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0003_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (508532980103/250000000000 : ℝ) ≤ 4*Real.exp (1/16 : ℝ)*Real.exp (-mu (radius 7 (9/128 : ℝ))) ∧ (2019/1000 : ℝ) < (508532980103/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0003_exp_radius
  have hrNumeric : (495002818041/500000000000 : ℝ) ≤ Real.exp (-9/896 : ℝ) ∧ Real.exp (-9/896 : ℝ) ≤ (990005636083/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (495002818041/500000000000 : ℝ) ≤ (radius 7 (9/128 : ℝ)) ∧ (radius 7 (9/128 : ℝ)) ≤ (990005636083/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9/128 : ℝ)) (495002818041/500000000000 : ℝ) (990005636083/1000000000000 : ℝ) (28205560107/200000000000 : ℝ) (141027800543/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9/128 : ℝ)) (495002818041/500000000000 : ℝ) (990005636083/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (495002818041/500000000000 : ℝ) (990005636083/1000000000000 : ℝ) (995002818041/1000000000000 : ℝ) (497501409021/500000000000 : ℝ) (49749513467/50000000000 : ℝ) (994990269341/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9/128 : ℝ)) 1 (995002818041/1000000000000 : ℝ) (497501409021/500000000000 : ℝ) (49749513467/50000000000 : ℝ) (994990269341/1000000000000 : ℝ) (99499654369/100000000000 : ℝ) (248749135923/250000000000 : ℝ) (99499654367/100000000000 : ℝ) (124374567959/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9/128 : ℝ)) 2 (99499654369/100000000000 : ℝ) (248749135923/250000000000 : ℝ) (99499654367/100000000000 : ℝ) (124374567959/125000000000 : ℝ) (3109364199/3125000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9/128 : ℝ)) 3 (3109364199/3125000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9/128 : ℝ)) 4 (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9/128 : ℝ)) 5 (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9/128 : ℝ)) 6 (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9/128 : ℝ)) 7 (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9/128 : ℝ))) (28205560107/200000000000 : ℝ) (141027800543/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (28205560107/200000000000 : ℝ) (141027800543/1000000000000 : ℝ) (570513900267/1000000000000 : ℝ) (35657118767/62500000000 : ℝ) (375536683341/1000000000000 : ℝ) (46942085419/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 1 (570513900267/1000000000000 : ℝ) (35657118767/62500000000 : ℝ) (375536683341/1000000000000 : ℝ) (46942085419/125000000000 : ℝ) (118256322951/250000000000 : ℝ) (118256322953/250000000000 : ℝ) (462870281943/1000000000000 : ℝ) (462870281953/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 2 (118256322951/250000000000 : ℝ) (118256322953/250000000000 : ℝ) (462870281943/1000000000000 : ℝ) (462870281953/1000000000000 : ℝ) (467947786873/1000000000000 : ℝ) (467947786883/1000000000000 : ℝ) (3743361913/8000000000 : ℝ) (93584047827/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 3 (467947786873/1000000000000 : ℝ) (467947786883/1000000000000 : ℝ) (3743361913/8000000000 : ℝ) (93584047827/200000000000 : ℝ) (467934012999/1000000000000 : ℝ) (467934013009/1000000000000 : ℝ) (116983503199/250000000000 : ℝ) (467934012807/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 4 (467934012999/1000000000000 : ℝ) (467934013009/1000000000000 : ℝ) (116983503199/250000000000 : ℝ) (467934012807/1000000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 5 (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 6 (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9/128 : ℝ))) 7 (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9/128 : ℝ)) hmem 8 (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9/128 : ℝ))) hcmem 8 (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9/128 : ℝ)) (994996543679/1000000000000 : ℝ) (497498271841/500000000000 : ℝ) (467934012897/1000000000000 : ℝ) (116983503227/250000000000 : ℝ) (738725207949/1000000000000 : ℝ) (73872520797/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0003_exp_lower
  have heNumeric : (508532980103/250000000000 : ℝ)/4 ≤ Real.exp (-67622520797/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (508532980103/250000000000 : ℝ)/4 ≤ Real.exp ((1/16 : ℝ)-(73872520797/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1/16 : ℝ) (9/128 : ℝ) (73872520797/100000000000 : ℝ) (508532980103/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0004; no trusted numerical premise.
theorem cover7_leaf0004_exp_radius : (499302941699481683/500000000000000000 : ℝ) ≤ Real.exp ((-5/448 : ℝ)/8) ∧ Real.exp ((-5/448 : ℝ)/8) ≤ (998605883398963367/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0004_exp_lower : (918483506543087149/1000000000000000000 : ℝ) ≤ Real.exp ((-680250651491/1000000000000 : ℝ)/8) ∧ Real.exp ((-680250651491/1000000000000 : ℝ)/8) ≤ (18369670130861743/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-680250651491/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0004_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (253245011987/125000000000 : ℝ) ≤ 4*Real.exp (9/128 : ℝ)*Real.exp (-mu (radius 7 (5/64 : ℝ))) ∧ (2019/1000 : ℝ) < (253245011987/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (5/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0004_exp_radius
  have hrNumeric : (988901335431/1000000000000 : ℝ) ≤ Real.exp (-5/448 : ℝ) ∧ Real.exp (-5/448 : ℝ) ≤ (123612666929/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (988901335431/1000000000000 : ℝ) ≤ (radius 7 (5/64 : ℝ)) ∧ (radius 7 (5/64 : ℝ)) ≤ (123612666929/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (5/64 : ℝ)) (988901335431/1000000000000 : ℝ) (123612666929/125000000000 : ℝ) (37143428743/250000000000 : ℝ) (7428685749/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (5/64 : ℝ)) (988901335431/1000000000000 : ℝ) (123612666929/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (5/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (988901335431/1000000000000 : ℝ) (123612666929/125000000000 : ℝ) (198890133543/200000000000 : ℝ) (248612666929/250000000000 : ℝ) (994435184127/1000000000000 : ℝ) (994435184129/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (5/64 : ℝ)) 1 (198890133543/200000000000 : ℝ) (248612666929/250000000000 : ℝ) (994435184127/1000000000000 : ℝ) (994435184129/1000000000000 : ℝ) (994442925921/1000000000000 : ℝ) (994442925923/1000000000000 : ℝ) (99444292589/100000000000 : ℝ) (994442925893/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (5/64 : ℝ)) 2 (994442925921/1000000000000 : ℝ) (994442925923/1000000000000 : ℝ) (99444292589/100000000000 : ℝ) (994442925893/1000000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (5/64 : ℝ)) 3 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (5/64 : ℝ)) 4 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (5/64 : ℝ)) 5 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (5/64 : ℝ)) 6 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (5/64 : ℝ)) 7 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (5/64 : ℝ))) (37143428743/250000000000 : ℝ) (7428685749/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37143428743/250000000000 : ℝ) (7428685749/50000000000 : ℝ) (287143428743/500000000000 : ℝ) (57428685749/100000000000 : ℝ) (385452610539/1000000000000 : ℝ) (385452610551/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 1 (287143428743/500000000000 : ℝ) (57428685749/100000000000 : ℝ) (385452610539/1000000000000 : ℝ) (385452610551/1000000000000 : ℝ) (119967433503/250000000000 : ℝ) (479869734021/1000000000000 : ℝ) (470489498731/1000000000000 : ℝ) (470489498741/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 2 (119967433503/250000000000 : ℝ) (479869734021/1000000000000 : ℝ) (470489498731/1000000000000 : ℝ) (470489498741/1000000000000 : ℝ) (475179616371/1000000000000 : ℝ) (475179616381/1000000000000 : ℝ) (475156469609/1000000000000 : ℝ) (475156469619/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 3 (475179616371/1000000000000 : ℝ) (475179616381/1000000000000 : ℝ) (475156469609/1000000000000 : ℝ) (475156469619/1000000000000 : ℝ) (47516804299/100000000000 : ℝ) (475168043/1000000000 : ℝ) (475168042849/1000000000000 : ℝ) (23758402143/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 4 (47516804299/100000000000 : ℝ) (475168043/1000000000 : ℝ) (475168042849/1000000000000 : ℝ) (23758402143/50000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 5 (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 6 (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (5/64 : ℝ))) 7 (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (5/64 : ℝ)) hmem 8 (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (5/64 : ℝ))) hcmem 8 (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (5/64 : ℝ)) (198888585181/200000000000 : ℝ) (248610731477/250000000000 : ℝ) (475168042919/1000000000000 : ℝ) (47516804293/100000000000 : ℝ) (75056315147/100000000000 : ℝ) (750563151491/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0004_exp_lower
  have heNumeric : (253245011987/125000000000 : ℝ)/4 ≤ Real.exp (-680250651491/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (253245011987/125000000000 : ℝ)/4 ≤ Real.exp ((9/128 : ℝ)-(750563151491/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9/128 : ℝ) (5/64 : ℝ) (750563151491/1000000000000 : ℝ) (253245011987/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0005; no trusted numerical premise.
theorem cover7_leaf0005_exp_radius : (998466578679457271/1000000000000000000 : ℝ) ≤ Real.exp ((-11/896 : ℝ)/8) ∧ Real.exp ((-11/896 : ℝ)/8) ≤ (124808322334932159/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0005_exp_lower : (57382061830079343/62500000000000000 : ℝ) ≤ Real.exp ((-683478511439/1000000000000 : ℝ)/8) ∧ Real.exp ((-683478511439/1000000000000 : ℝ)/8) ≤ (918112989281269489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683478511439/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0005_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100971556171/50000000000 : ℝ) ≤ 4*Real.exp (5/64 : ℝ)*Real.exp (-mu (radius 7 (11/128 : ℝ))) ∧ (2019/1000 : ℝ) < (100971556171/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (11/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0005_exp_radius
  have hrNumeric : (987798266571/1000000000000 : ℝ) ≤ Real.exp (-11/896 : ℝ) ∧ Real.exp (-11/896 : ℝ) ≤ (246949566643/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (987798266571/1000000000000 : ℝ) ≤ (radius 7 (11/128 : ℝ)) ∧ (radius 7 (11/128 : ℝ)) ≤ (246949566643/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (11/128 : ℝ)) (987798266571/1000000000000 : ℝ) (246949566643/250000000000 : ℝ) (77869417227/500000000000 : ℝ) (77869417231/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (11/128 : ℝ)) (987798266571/1000000000000 : ℝ) (246949566643/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (11/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (987798266571/1000000000000 : ℝ) (246949566643/250000000000 : ℝ) (198779826657/200000000000 : ℝ) (496949566643/500000000000 : ℝ) (198776081717/200000000000 : ℝ) (993880408587/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (11/128 : ℝ)) 1 (198779826657/200000000000 : ℝ) (496949566643/500000000000 : ℝ) (198776081717/200000000000 : ℝ) (993880408587/1000000000000 : ℝ) (198777954187/200000000000 : ℝ) (993889770937/1000000000000 : ℝ) (99388977089/100000000000 : ℝ) (993889770893/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (11/128 : ℝ)) 2 (198777954187/200000000000 : ℝ) (993889770937/1000000000000 : ℝ) (99388977089/100000000000 : ℝ) (993889770893/1000000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (11/128 : ℝ)) 3 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (11/128 : ℝ)) 4 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (11/128 : ℝ)) 5 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (11/128 : ℝ)) 6 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (11/128 : ℝ)) 7 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (11/128 : ℝ))) (77869417227/500000000000 : ℝ) (77869417231/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (77869417227/500000000000 : ℝ) (77869417231/500000000000 : ℝ) (577869417227/1000000000000 : ℝ) (577869417231/1000000000000 : ℝ) (78927519777/200000000000 : ℝ) (24664849931/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 1 (577869417227/1000000000000 : ℝ) (577869417231/1000000000000 : ℝ) (78927519777/200000000000 : ℝ) (24664849931/62500000000 : ℝ) (60781688507/125000000000 : ℝ) (15195422127/31250000000 : ℝ) (477544761549/1000000000000 : ℝ) (238772380779/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 2 (60781688507/125000000000 : ℝ) (15195422127/31250000000 : ℝ) (477544761549/1000000000000 : ℝ) (238772380779/500000000000 : ℝ) (240949567401/500000000000 : ℝ) (481899134811/1000000000000 : ℝ) (240939730823/500000000000 : ℝ) (60234932707/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 3 (240949567401/500000000000 : ℝ) (481899134811/1000000000000 : ℝ) (240939730823/500000000000 : ℝ) (60234932707/125000000000 : ℝ) (30118081139/62500000000 : ℝ) (240944649117/500000000000 : ℝ) (481889298123/1000000000000 : ℝ) (240944649067/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 4 (30118081139/62500000000 : ℝ) (240944649117/500000000000 : ℝ) (481889298123/1000000000000 : ℝ) (240944649067/500000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 5 (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 6 (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (11/128 : ℝ))) 7 (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (11/128 : ℝ)) hmem 8 (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (11/128 : ℝ))) hcmem 8 (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (11/128 : ℝ)) (31059055341/31250000000 : ℝ) (198777954183/200000000000 : ℝ) (481889298173/1000000000000 : ℝ) (60236162273/125000000000 : ℝ) (380801755709/500000000000 : ℝ) (761603511439/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0005_exp_lower
  have heNumeric : (100971556171/50000000000 : ℝ)/4 ≤ Real.exp (-683478511439/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100971556171/50000000000 : ℝ)/4 ≤ Real.exp ((5/64 : ℝ)-(761603511439/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (5/64 : ℝ) (11/128 : ℝ) (761603511439/1000000000000 : ℝ) (100971556171/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0006; no trusted numerical premise.
theorem cover7_leaf0006_exp_radius : (998396933607209887/1000000000000000000 : ℝ) ≤ Real.exp ((-23/1792 : ℝ)/8) ∧ Real.exp ((-23/1792 : ℝ)/8) ≤ (31199904175225309/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-23/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0006_exp_lower : (459202931360753983/500000000000000000 : ℝ) ≤ Real.exp ((-136185391699/200000000000 : ℝ)/8) ∧ Real.exp ((-136185391699/200000000000 : ℝ)/8) ≤ (918405862721507967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136185391699/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0006_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2024590388117/1000000000000 : ℝ) ≤ 4*Real.exp (11/128 : ℝ)*Real.exp (-mu (radius 7 (23/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2024590388117/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (23/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0006_exp_radius
  have hrNumeric : (493623596817/500000000000 : ℝ) ≤ Real.exp (-23/1792 : ℝ) ∧ Real.exp (-23/1792 : ℝ) ≤ (197449438727/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (493623596817/500000000000 : ℝ) ≤ (radius 7 (23/256 : ℝ)) ∧ (radius 7 (23/256 : ℝ)) ≤ (197449438727/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (23/256 : ℝ)) (493623596817/500000000000 : ℝ) (197449438727/200000000000 : ℝ) (159194782137/1000000000000 : ℝ) (2487418471/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (23/256 : ℝ)) (493623596817/500000000000 : ℝ) (197449438727/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (23/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (493623596817/500000000000 : ℝ) (197449438727/200000000000 : ℝ) (993623596817/1000000000000 : ℝ) (496811798409/500000000000 : ℝ) (124200392111/125000000000 : ℝ) (993603136889/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (23/256 : ℝ)) 1 (993623596817/1000000000000 : ℝ) (496811798409/500000000000 : ℝ) (124200392111/125000000000 : ℝ) (993603136889/1000000000000 : ℝ) (248403341713/250000000000 : ℝ) (496806683427/500000000000 : ℝ) (993613366799/1000000000000 : ℝ) (993613366801/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (23/256 : ℝ)) 2 (248403341713/250000000000 : ℝ) (496806683427/500000000000 : ℝ) (993613366799/1000000000000 : ℝ) (993613366801/1000000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (23/256 : ℝ)) 3 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (23/256 : ℝ)) 4 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (23/256 : ℝ)) 5 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (23/256 : ℝ)) 6 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (23/256 : ℝ)) 7 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (23/256 : ℝ))) (159194782137/1000000000000 : ℝ) (2487418471/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (159194782137/1000000000000 : ℝ) (2487418471/15625000000 : ℝ) (144899347767/250000000000 : ℝ) (18112418471/31250000000 : ℝ) (79798441623/200000000000 : ℝ) (638387533/1600000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 1 (144899347767/250000000000 : ℝ) (18112418471/31250000000 : ℝ) (79798441623/200000000000 : ℝ) (638387533/1600000000 : ℝ) (489294799591/1000000000000 : ℝ) (489294799599/1000000000000 : ℝ) (240444818451/500000000000 : ℝ) (48088963691/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 2 (489294799591/1000000000000 : ℝ) (489294799599/1000000000000 : ℝ) (240444818451/500000000000 : ℝ) (48088963691/100000000000 : ℝ) (242546109123/500000000000 : ℝ) (97018443651/200000000000 : ℝ) (242537006719/500000000000 : ℝ) (485074013447/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 3 (242546109123/500000000000 : ℝ) (97018443651/200000000000 : ℝ) (242537006719/500000000000 : ℝ) (485074013447/1000000000000 : ℝ) (242541557921/500000000000 : ℝ) (485083115851/1000000000000 : ℝ) (121270778939/250000000000 : ℝ) (242541557883/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 4 (242541557921/500000000000 : ℝ) (485083115851/1000000000000 : ℝ) (121270778939/250000000000 : ℝ) (242541557883/500000000000 : ℝ) (485083115799/1000000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 5 (485083115799/1000000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 6 (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (23/256 : ℝ))) 7 (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (23/256 : ℝ)) hmem 8 (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (23/256 : ℝ))) hcmem 8 (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (23/256 : ℝ)) (39744534673/40000000000 : ℝ) (248403341707/250000000000 : ℝ) (242541557899/500000000000 : ℝ) (485083115809/1000000000000 : ℝ) (383432229237/500000000000 : ℝ) (153372891699/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0006_exp_lower
  have heNumeric : (2024590388117/1000000000000 : ℝ)/4 ≤ Real.exp (-136185391699/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2024590388117/1000000000000 : ℝ)/4 ≤ Real.exp ((11/128 : ℝ)-(153372891699/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (11/128 : ℝ) (23/256 : ℝ) (153372891699/200000000000 : ℝ) (2024590388117/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0007; no trusted numerical premise.
theorem cover7_leaf0007_exp_radius : (31197727918526493/31250000000000000 : ℝ) ≤ Real.exp ((-3/224 : ℝ)/8) ∧ Real.exp ((-3/224 : ℝ)/8) ≤ (998327293392847777/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/224 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0007_exp_lower : (183653638143474219/200000000000000000 : ℝ) ≤ Real.exp ((-341063137109/500000000000 : ℝ)/8) ∧ Real.exp ((-341063137109/500000000000 : ℝ)/8) ≤ (114783523839671387/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341063137109/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0007_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2022163720493/1000000000000 : ℝ) ≤ 4*Real.exp (23/256 : ℝ)*Real.exp (-mu (radius 7 (3/32 : ℝ))) ∧ (2019/1000 : ℝ) < (2022163720493/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (3/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0007_exp_radius
  have hrNumeric : (30834263379/31250000000 : ℝ) ≤ Real.exp (-3/224 : ℝ) ∧ Real.exp (-3/224 : ℝ) ≤ (986696428129/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30834263379/31250000000 : ℝ) ≤ (radius 7 (3/32 : ℝ)) ∧ (radius 7 (3/32 : ℝ)) ≤ (986696428129/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (3/32 : ℝ)) (30834263379/31250000000 : ℝ) (986696428129/1000000000000 : ℝ) (1016084679/6250000000 : ℝ) (162573548647/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (3/32 : ℝ)) (30834263379/31250000000 : ℝ) (986696428129/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (3/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30834263379/31250000000 : ℝ) (986696428129/1000000000000 : ℝ) (62084263379/62500000000 : ℝ) (198669642813/200000000000 : ℝ) (496662971271/500000000000 : ℝ) (62082871409/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (3/32 : ℝ)) 1 (62084263379/62500000000 : ℝ) (198669642813/200000000000 : ℝ) (496662971271/500000000000 : ℝ) (62082871409/62500000000 : ℝ) (993337078303/1000000000000 : ℝ) (198667415661/200000000000 : ℝ) (6208356739/6250000000 : ℝ) (993337078243/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (3/32 : ℝ)) 2 (993337078303/1000000000000 : ℝ) (198667415661/200000000000 : ℝ) (6208356739/6250000000 : ℝ) (993337078243/1000000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (3/32 : ℝ)) 3 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (3/32 : ℝ)) 4 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (3/32 : ℝ)) 5 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (3/32 : ℝ)) 6 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (3/32 : ℝ)) 7 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (3/32 : ℝ))) (1016084679/6250000000 : ℝ) (162573548647/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1016084679/6250000000 : ℝ) (162573548647/1000000000000 : ℝ) (7266084679/12500000000 : ℝ) (145321693581/250000000000 : ℝ) (80640820591/200000000000 : ℝ) (100801025741/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 1 (7266084679/12500000000 : ℝ) (145321693581/250000000000 : ℝ) (80640820591/200000000000 : ℝ) (100801025741/250000000000 : ℝ) (492245438637/1000000000000 : ℝ) (123061359661/250000000000 : ℝ) (242062601613/500000000000 : ℝ) (242062601617/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 2 (492245438637/1000000000000 : ℝ) (123061359661/250000000000 : ℝ) (242062601613/500000000000 : ℝ) (242062601617/500000000000 : ℝ) (488185320931/1000000000000 : ℝ) (488185320939/1000000000000 : ℝ) (488168437137/1000000000000 : ℝ) (97633687429/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 3 (488185320931/1000000000000 : ℝ) (488185320939/1000000000000 : ℝ) (488168437137/1000000000000 : ℝ) (97633687429/200000000000 : ℝ) (244088439517/500000000000 : ℝ) (244088439521/500000000000 : ℝ) (488176878961/1000000000000 : ℝ) (48817687897/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 4 (244088439517/500000000000 : ℝ) (244088439521/500000000000 : ℝ) (488176878961/1000000000000 : ℝ) (48817687897/100000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 5 (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 6 (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (3/32 : ℝ))) 7 (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (3/32 : ℝ)) hmem 8 (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (3/32 : ℝ))) hcmem 8 (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (3/32 : ℝ)) (993337078271/1000000000000 : ℝ) (496668539137/500000000000 : ℝ) (488176878997/1000000000000 : ℝ) (244088439503/500000000000 : ℝ) (3859850121/5000000000 : ℝ) (385985012109/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0007_exp_lower
  have heNumeric : (2022163720493/1000000000000 : ℝ)/4 ≤ Real.exp (-341063137109/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2022163720493/1000000000000 : ℝ)/4 ≤ Real.exp ((23/256 : ℝ)-(385985012109/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (23/256 : ℝ) (3/32 : ℝ) (385985012109/500000000000 : ℝ) (2022163720493/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0008; no trusted numerical premise.
theorem cover7_leaf0008_exp_radius : (998257658036032091/1000000000000000000 : ℝ) ≤ Real.exp ((-25/1792 : ℝ)/8) ∧ Real.exp ((-25/1792 : ℝ)/8) ≤ (249564414509008023/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-25/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0008_exp_lower : (114768385613449553/125000000000000000 : ℝ) ≤ Real.exp ((-683181423881/1000000000000 : ℝ)/8) ∧ Real.exp ((-683181423881/1000000000000 : ℝ)/8) ≤ (36725883396303857/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683181423881/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0008_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252503895051/125000000000 : ℝ) ≤ 4*Real.exp (3/32 : ℝ)*Real.exp (-mu (radius 7 (25/256 : ℝ))) ∧ (2019/1000 : ℝ) < (252503895051/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (25/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0008_exp_radius
  have hrNumeric : (246536492471/250000000000 : ℝ) ≤ Real.exp (-25/1792 : ℝ) ∧ Real.exp (-25/1792 : ℝ) ≤ (197229193977/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246536492471/250000000000 : ℝ) ≤ (radius 7 (25/256 : ℝ)) ∧ (radius 7 (25/256 : ℝ)) ≤ (197229193977/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (25/256 : ℝ)) (246536492471/250000000000 : ℝ) (197229193977/200000000000 : ℝ) (165879854351/1000000000000 : ℝ) (82939927179/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (25/256 : ℝ)) (246536492471/250000000000 : ℝ) (197229193977/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (25/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246536492471/250000000000 : ℝ) (197229193977/200000000000 : ℝ) (496536492471/500000000000 : ℝ) (993072984943/1000000000000 : ℝ) (124131103191/125000000000 : ℝ) (99304882553/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (25/256 : ℝ)) 1 (496536492471/500000000000 : ℝ) (993072984943/1000000000000 : ℝ) (124131103191/125000000000 : ℝ) (99304882553/100000000000 : ℝ) (198612181047/200000000000 : ℝ) (993060905237/1000000000000 : ℝ) (993060905161/1000000000000 : ℝ) (248265226291/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (25/256 : ℝ)) 2 (198612181047/200000000000 : ℝ) (993060905237/1000000000000 : ℝ) (993060905161/1000000000000 : ℝ) (248265226291/250000000000 : ℝ) (496530452599/500000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (25/256 : ℝ)) 3 (496530452599/500000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (25/256 : ℝ)) 4 (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (25/256 : ℝ)) 5 (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (25/256 : ℝ)) 6 (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (25/256 : ℝ)) 7 (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (25/256 : ℝ))) (165879854351/1000000000000 : ℝ) (82939927179/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (165879854351/1000000000000 : ℝ) (82939927179/500000000000 : ℝ) (23317597087/40000000000 : ℝ) (582939927179/1000000000000 : ℝ) (6363804783/15625000000 : ℝ) (407283506121/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 1 (23317597087/40000000000 : ℝ) (582939927179/1000000000000 : ℝ) (6363804783/15625000000 : ℝ) (407283506121/1000000000000 : ℝ) (495111716643/1000000000000 : ℝ) (9902234333/20000000000 : ℝ) (19490379879/40000000000 : ℝ) (487259496983/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 2 (495111716643/1000000000000 : ℝ) (9902234333/20000000000 : ℝ) (19490379879/40000000000 : ℝ) (487259496983/1000000000000 : ℝ) (491185606809/1000000000000 : ℝ) (491185606817/1000000000000 : ℝ) (491169915607/1000000000000 : ℝ) (15349059863/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 3 (491185606809/1000000000000 : ℝ) (491185606817/1000000000000 : ℝ) (491169915607/1000000000000 : ℝ) (15349059863/31250000000 : ℝ) (61397220151/125000000000 : ℝ) (491177761217/1000000000000 : ℝ) (98235552229/200000000000 : ℝ) (245588880577/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 4 (61397220151/125000000000 : ℝ) (491177761217/1000000000000 : ℝ) (98235552229/200000000000 : ℝ) (245588880577/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 5 (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 6 (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (25/256 : ℝ))) 7 (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (25/256 : ℝ)) hmem 8 (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (25/256 : ℝ))) hcmem 8 (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (25/256 : ℝ)) (993060905197/1000000000000 : ℝ) (993060905201/1000000000000 : ℝ) (61397220147/125000000000 : ℝ) (245588880593/500000000000 : ℝ) (776931423861/1000000000000 : ℝ) (776931423881/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0008_exp_lower
  have heNumeric : (252503895051/125000000000 : ℝ)/4 ≤ Real.exp (-683181423881/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252503895051/125000000000 : ℝ)/4 ≤ Real.exp ((3/32 : ℝ)-(776931423881/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (3/32 : ℝ) (25/256 : ℝ) (776931423881/1000000000000 : ℝ) (252503895051/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0009; no trusted numerical premise.
theorem cover7_leaf0009_exp_radius : (39928913687163931/40000000000000000 : ℝ) ≤ Real.exp ((-51/3584 : ℝ)/8) ∧ Real.exp ((-51/3584 : ℝ)/8) ≤ (249555710544774569/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-51/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0009_exp_lower : (918316550055150831/1000000000000000000 : ℝ) ≤ Real.exp ((-340852488129/500000000000 : ℝ)/8) ∧ Real.exp ((-340852488129/500000000000 : ℝ)/8) ≤ (57394784378446927/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-340852488129/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0009_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505753958357/250000000000 : ℝ) ≤ 4*Real.exp (25/256 : ℝ)*Real.exp (-mu (radius 7 (51/512 : ℝ))) ∧ (2019/1000 : ℝ) < (505753958357/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (51/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0009_exp_radius
  have hrNumeric : (246467713983/250000000000 : ℝ) ≤ Real.exp (-51/3584 : ℝ) ∧ Real.exp (-51/3584 : ℝ) ≤ (985870855933/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246467713983/250000000000 : ℝ) ≤ (radius 7 (51/512 : ℝ)) ∧ (radius 7 (51/512 : ℝ)) ≤ (985870855933/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (51/512 : ℝ)) (246467713983/250000000000 : ℝ) (985870855933/1000000000000 : ℝ) (16750718021/100000000000 : ℝ) (20938397527/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (51/512 : ℝ)) (246467713983/250000000000 : ℝ) (985870855933/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (51/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246467713983/250000000000 : ℝ) (985870855933/1000000000000 : ℝ) (496467713983/500000000000 : ℝ) (992935427967/1000000000000 : ℝ) (496455148007/500000000000 : ℝ) (62056893501/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (51/512 : ℝ)) 1 (496467713983/500000000000 : ℝ) (992935427967/1000000000000 : ℝ) (496455148007/500000000000 : ℝ) (62056893501/62500000000 : ℝ) (99292286199/100000000000 : ℝ) (124115357749/125000000000 : ℝ) (99292286191/100000000000 : ℝ) (124115357739/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (51/512 : ℝ)) 2 (99292286199/100000000000 : ℝ) (124115357749/125000000000 : ℝ) (99292286191/100000000000 : ℝ) (124115357739/125000000000 : ℝ) (19858457239/20000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (51/512 : ℝ)) 3 (19858457239/20000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (51/512 : ℝ)) 4 (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (51/512 : ℝ)) 5 (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (51/512 : ℝ)) 6 (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (51/512 : ℝ)) 7 (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (51/512 : ℝ))) (16750718021/100000000000 : ℝ) (20938397527/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (16750718021/100000000000 : ℝ) (20938397527/125000000000 : ℝ) (116750718021/200000000000 : ℝ) (145938397527/250000000000 : ℝ) (204638205261/500000000000 : ℝ) (40927641053/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 1 (116750718021/200000000000 : ℝ) (145938397527/250000000000 : ℝ) (204638205261/500000000000 : ℝ) (40927641053/100000000000 : ℝ) (496515000313/1000000000000 : ℝ) (496515000319/1000000000000 : ℝ) (244395465377/500000000000 : ℝ) (488790930761/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 2 (496515000313/1000000000000 : ℝ) (496515000319/1000000000000 : ℝ) (244395465377/500000000000 : ℝ) (488790930761/1000000000000 : ℝ) (492652965533/1000000000000 : ℝ) (24632648277/50000000000 : ℝ) (492637827553/1000000000000 : ℝ) (12315945689/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 3 (492652965533/1000000000000 : ℝ) (24632648277/50000000000 : ℝ) (492637827553/1000000000000 : ℝ) (12315945689/25000000000 : ℝ) (492645396543/1000000000000 : ℝ) (9852907931/20000000000 : ℝ) (123161349121/250000000000 : ℝ) (123161349123/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 4 (492645396543/1000000000000 : ℝ) (9852907931/20000000000 : ℝ) (123161349121/250000000000 : ℝ) (123161349123/250000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 5 (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 6 (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (51/512 : ℝ))) 7 (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (51/512 : ℝ)) hmem 8 (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (51/512 : ℝ))) hcmem 8 (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (51/512 : ℝ)) (992922861949/1000000000000 : ℝ) (7757209859/7812500000 : ℝ) (492645396513/1000000000000 : ℝ) (492645396521/1000000000000 : ℝ) (389680613121/500000000000 : ℝ) (389680613129/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0009_exp_lower
  have heNumeric : (505753958357/250000000000 : ℝ)/4 ≤ Real.exp (-340852488129/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505753958357/250000000000 : ℝ)/4 ≤ Real.exp ((25/256 : ℝ)-(389680613129/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (25/256 : ℝ) (51/512 : ℝ) (389680613129/500000000000 : ℝ) (505753958357/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0010; no trusted numerical premise.
theorem cover7_leaf0010_exp_radius : (124773503442053001/125000000000000000 : ℝ) ≤ Real.exp ((-13/896 : ℝ)/8) ∧ Real.exp ((-13/896 : ℝ)/8) ≤ (998188027536424009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0010_exp_lower : (459132775425758421/500000000000000000 : ℝ) ≤ Real.exp ((-682149272899/1000000000000 : ℝ)/8) ∧ Real.exp ((-682149272899/1000000000000 : ℝ)/8) ≤ (918265550851516843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682149272899/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0010_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (202211721393/100000000000 : ℝ) ≤ 4*Real.exp (51/512 : ℝ)*Real.exp (-mu (radius 7 (13/128 : ℝ))) ∧ (2019/1000 : ℝ) < (202211721393/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (13/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0010_exp_radius
  have hrNumeric : (98559581873/100000000000 : ℝ) ≤ Real.exp (-13/896 : ℝ) ∧ Real.exp (-13/896 : ℝ) ≤ (985595818731/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98559581873/100000000000 : ℝ) ≤ (radius 7 (13/128 : ℝ)) ∧ (radius 7 (13/128 : ℝ)) ≤ (985595818731/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (13/128 : ℝ)) (98559581873/100000000000 : ℝ) (985595818731/1000000000000 : ℝ) (2642468019/15625000000 : ℝ) (84558976611/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (13/128 : ℝ)) (98559581873/100000000000 : ℝ) (985595818731/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (13/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98559581873/100000000000 : ℝ) (985595818731/1000000000000 : ℝ) (198559581873/200000000000 : ℝ) (496398954683/500000000000 : ℝ) (31024118307/31250000000 : ℝ) (496385892913/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (13/128 : ℝ)) 1 (198559581873/200000000000 : ℝ) (496398954683/500000000000 : ℝ) (31024118307/31250000000 : ℝ) (496385892913/500000000000 : ℝ) (496392423797/500000000000 : ℝ) (248196211899/250000000000 : ℝ) (248196211877/250000000000 : ℝ) (992784847511/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (13/128 : ℝ)) 2 (496392423797/500000000000 : ℝ) (248196211899/250000000000 : ℝ) (248196211877/250000000000 : ℝ) (992784847511/1000000000000 : ℝ) (992784847551/1000000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (13/128 : ℝ)) 3 (992784847551/1000000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (13/128 : ℝ)) 4 (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (13/128 : ℝ)) 5 (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (13/128 : ℝ)) 6 (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (13/128 : ℝ)) 7 (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (13/128 : ℝ))) (2642468019/15625000000 : ℝ) (84558976611/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2642468019/15625000000 : ℝ) (84558976611/500000000000 : ℝ) (18267468019/31250000000 : ℝ) (584558976611/1000000000000 : ℝ) (102809883163/250000000000 : ℝ) (20561976633/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 1 (18267468019/31250000000 : ℝ) (584558976611/1000000000000 : ℝ) (102809883163/250000000000 : ℝ) (20561976633/50000000000 : ℝ) (49789925463/100000000000 : ℝ) (124474813659/250000000000 : ℝ) (19611986553/40000000000 : ℝ) (61287457979/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 2 (49789925463/100000000000 : ℝ) (124474813659/250000000000 : ℝ) (19611986553/40000000000 : ℝ) (61287457979/125000000000 : ℝ) (494099459227/1000000000000 : ℝ) (247049729617/500000000000 : ℝ) (247042424071/500000000000 : ℝ) (494084848149/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 3 (494099459227/1000000000000 : ℝ) (247049729617/500000000000 : ℝ) (247042424071/500000000000 : ℝ) (494084848149/1000000000000 : ℝ) (123523038421/250000000000 : ℝ) (123523038423/250000000000 : ℝ) (49409215363/100000000000 : ℝ) (247046076819/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 4 (123523038421/250000000000 : ℝ) (123523038423/250000000000 : ℝ) (49409215363/100000000000 : ℝ) (247046076819/500000000000 : ℝ) (494092153657/1000000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 5 (494092153657/1000000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 6 (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (13/128 : ℝ))) 7 (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (13/128 : ℝ)) hmem 8 (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (13/128 : ℝ))) hcmem 8 (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (13/128 : ℝ)) (19855696951/20000000000 : ℝ) (496392423777/500000000000 : ℝ) (61761519207/125000000000 : ℝ) (98818430733/200000000000 : ℝ) (781758647881/1000000000000 : ℝ) (781758647899/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0010_exp_lower
  have heNumeric : (202211721393/100000000000 : ℝ)/4 ≤ Real.exp (-682149272899/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (202211721393/100000000000 : ℝ)/4 ≤ Real.exp ((51/512 : ℝ)-(781758647899/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (51/512 : ℝ) (13/128 : ℝ) (781758647899/1000000000000 : ℝ) (202211721393/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0011; no trusted numerical premise.
theorem cover7_leaf0011_exp_radius : (499076607053983471/500000000000000000 : ℝ) ≤ Real.exp ((-53/3584 : ℝ)/8) ∧ Real.exp ((-53/3584 : ℝ)/8) ≤ (998153214107966943/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-53/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0011_exp_lower : (918218146377808879/1000000000000000000 : ℝ) ≤ Real.exp ((-27302490999/40000000000 : ℝ)/8) ∧ Real.exp ((-27302490999/40000000000 : ℝ)/8) ≤ (11477726829722611/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27302490999/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0011_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505320561939/250000000000 : ℝ) ≤ 4*Real.exp (13/128 : ℝ)*Real.exp (-mu (radius 7 (53/512 : ℝ))) ∧ (2019/1000 : ℝ) < (505320561939/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (53/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0011_exp_radius
  have hrNumeric : (492660429129/500000000000 : ℝ) ≤ Real.exp (-53/3584 : ℝ) ∧ Real.exp (-53/3584 : ℝ) ≤ (985320858259/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492660429129/500000000000 : ℝ) ≤ (radius 7 (53/512 : ℝ)) ∧ (radius 7 (53/512 : ℝ)) ≤ (985320858259/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (53/512 : ℝ)) (492660429129/500000000000 : ℝ) (985320858259/1000000000000 : ℝ) (170712642413/1000000000000 : ℝ) (8535632121/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (53/512 : ℝ)) (492660429129/500000000000 : ℝ) (985320858259/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (53/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492660429129/500000000000 : ℝ) (985320858259/1000000000000 : ℝ) (992660429129/1000000000000 : ℝ) (99266042913/100000000000 : ℝ) (992633294957/1000000000000 : ℝ) (496316647479/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (53/512 : ℝ)) 1 (992660429129/1000000000000 : ℝ) (99266042913/100000000000 : ℝ) (992633294957/1000000000000 : ℝ) (496316647479/500000000000 : ℝ) (992646862043/1000000000000 : ℝ) (248161715511/250000000000 : ℝ) (19852937239/20000000000 : ℝ) (7755053609/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (53/512 : ℝ)) 2 (992646862043/1000000000000 : ℝ) (248161715511/250000000000 : ℝ) (19852937239/20000000000 : ℝ) (7755053609/7812500000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (53/512 : ℝ)) 3 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (53/512 : ℝ)) 4 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (53/512 : ℝ)) 5 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (53/512 : ℝ)) 6 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (53/512 : ℝ)) 7 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (53/512 : ℝ))) (170712642413/1000000000000 : ℝ) (8535632121/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (170712642413/1000000000000 : ℝ) (8535632121/50000000000 : ℝ) (292678160603/500000000000 : ℝ) (58535632121/100000000000 : ℝ) (413173864629/1000000000000 : ℝ) (413173864639/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 1 (292678160603/500000000000 : ℝ) (58535632121/100000000000 : ℝ) (413173864629/1000000000000 : ℝ) (413173864639/1000000000000 : ℝ) (499265092917/1000000000000 : ℝ) (19970603717/40000000000 : ℝ) (98357294273/200000000000 : ℝ) (491786471373/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 2 (499265092917/1000000000000 : ℝ) (19970603717/40000000000 : ℝ) (98357294273/200000000000 : ℝ) (491786471373/1000000000000 : ℝ) (495525782141/1000000000000 : ℝ) (495525782149/1000000000000 : ℝ) (123877918311/250000000000 : ℝ) (495511673253/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 3 (495525782141/1000000000000 : ℝ) (495525782149/1000000000000 : ℝ) (123877918311/250000000000 : ℝ) (495511673253/1000000000000 : ℝ) (123879681923/250000000000 : ℝ) (495518727701/1000000000000 : ℝ) (247759363821/500000000000 : ℝ) (495518727651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 4 (123879681923/250000000000 : ℝ) (495518727701/1000000000000 : ℝ) (247759363821/500000000000 : ℝ) (495518727651/1000000000000 : ℝ) (495518727667/1000000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 5 (495518727667/1000000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 6 (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (53/512 : ℝ))) 7 (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (53/512 : ℝ)) hmem 8 (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (53/512 : ℝ))) hcmem 8 (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (53/512 : ℝ)) (248161715499/250000000000 : ℝ) (496323430999/500000000000 : ℝ) (247759363833/500000000000 : ℝ) (123879681919/250000000000 : ℝ) (196031193739/250000000000 : ℝ) (31364990999/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0011_exp_lower
  have heNumeric : (505320561939/250000000000 : ℝ)/4 ≤ Real.exp (-27302490999/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505320561939/250000000000 : ℝ)/4 ≤ Real.exp ((13/128 : ℝ)-(31364990999/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (13/128 : ℝ) (53/512 : ℝ) (31364990999/40000000000 : ℝ) (505320561939/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0012; no trusted numerical premise.
theorem cover7_leaf0012_exp_radius : (998118401893684727/1000000000000000000 : ℝ) ≤ Real.exp ((-27/1792 : ℝ)/8) ∧ Real.exp ((-27/1792 : ℝ)/8) ≤ (124764800236710591/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0012_exp_lower : (918174217880208039/1000000000000000000 : ℝ) ≤ Real.exp ((-682945012333/1000000000000 : ℝ)/8) ∧ Real.exp ((-682945012333/1000000000000 : ℝ)/8) ≤ (22954355447005201/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682945012333/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0012_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505127193889/250000000000 : ℝ) ≤ 4*Real.exp (53/512 : ℝ)*Real.exp (-mu (radius 7 (27/256 : ℝ))) ∧ (2019/1000 : ℝ) < (505127193889/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (27/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0012_exp_radius
  have hrNumeric : (492522987247/500000000000 : ℝ) ≤ Real.exp (-27/1792 : ℝ) ∧ Real.exp (-27/1792 : ℝ) ≤ (197009194899/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492522987247/500000000000 : ℝ) ≤ (radius 7 (27/256 : ℝ)) ∧ (radius 7 (27/256 : ℝ)) ≤ (197009194899/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (27/256 : ℝ)) (492522987247/500000000000 : ℝ) (197009194899/200000000000 : ℝ) (172291694899/1000000000000 : ℝ) (34458338981/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (27/256 : ℝ)) (492522987247/500000000000 : ℝ) (197009194899/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (27/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492522987247/500000000000 : ℝ) (197009194899/200000000000 : ℝ) (992522987247/1000000000000 : ℝ) (62032686703/62500000000 : ℝ) (992494823409/1000000000000 : ℝ) (99249482341/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (27/256 : ℝ)) 1 (992522987247/1000000000000 : ℝ) (62032686703/62500000000 : ℝ) (992494823409/1000000000000 : ℝ) (99249482341/100000000000 : ℝ) (62031806583/62500000000 : ℝ) (992508905329/1000000000000 : ℝ) (248127226307/250000000000 : ℝ) (99250890523/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (27/256 : ℝ)) 2 (62031806583/62500000000 : ℝ) (992508905329/1000000000000 : ℝ) (248127226307/250000000000 : ℝ) (99250890523/100000000000 : ℝ) (496254452639/500000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (27/256 : ℝ)) 3 (496254452639/500000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (27/256 : ℝ)) 4 (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (27/256 : ℝ)) 5 (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (27/256 : ℝ)) 6 (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (27/256 : ℝ)) 7 (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (27/256 : ℝ))) (172291694899/1000000000000 : ℝ) (34458338981/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172291694899/1000000000000 : ℝ) (34458338981/200000000000 : ℝ) (586145847449/1000000000000 : ℝ) (586145847453/1000000000000 : ℝ) (207540173761/500000000000 : ℝ) (41508034753/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 1 (586145847449/1000000000000 : ℝ) (586145847453/1000000000000 : ℝ) (207540173761/500000000000 : ℝ) (41508034753/100000000000 : ℝ) (100122619497/200000000000 : ℝ) (125153274373/250000000000 : ℝ) (493252087737/1000000000000 : ℝ) (98650417549/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 2 (100122619497/200000000000 : ℝ) (125153274373/250000000000 : ℝ) (493252087737/1000000000000 : ℝ) (98650417549/200000000000 : ℝ) (496932592611/1000000000000 : ℝ) (496932592619/1000000000000 : ℝ) (124229740673/250000000000 : ℝ) (4969189627/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 3 (496932592611/1000000000000 : ℝ) (496932592619/1000000000000 : ℝ) (124229740673/250000000000 : ℝ) (4969189627/10000000000 : ℝ) (496925777651/1000000000000 : ℝ) (24846288883/50000000000 : ℝ) (124231444401/250000000000 : ℝ) (496925777613/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 4 (496925777651/1000000000000 : ℝ) (24846288883/50000000000 : ℝ) (124231444401/250000000000 : ℝ) (496925777613/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 5 (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 6 (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (27/256 : ℝ))) 7 (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (27/256 : ℝ)) hmem 8 (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (27/256 : ℝ))) hcmem 8 (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (27/256 : ℝ)) (992508905277/1000000000000 : ℝ) (3101590329/3125000000 : ℝ) (496925777627/1000000000000 : ℝ) (496925777637/1000000000000 : ℝ) (786460637313/1000000000000 : ℝ) (786460637333/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0012_exp_lower
  have heNumeric : (505127193889/250000000000 : ℝ)/4 ≤ Real.exp (-682945012333/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505127193889/250000000000 : ℝ)/4 ≤ Real.exp ((53/512 : ℝ)-(786460637333/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (53/512 : ℝ) (27/256 : ℝ) (786460637333/1000000000000 : ℝ) (505127193889/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0013; no trusted numerical premise.
theorem cover7_leaf0013_exp_radius : (998083590893535019/1000000000000000000 : ℝ) ≤ Real.exp ((-55/3584 : ℝ)/8) ∧ Real.exp ((-55/3584 : ℝ)/8) ≤ (49904179544676751/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-55/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0013_exp_lower : (918133652686611551/1000000000000000000 : ℝ) ≤ Real.exp ((-683298462377/1000000000000 : ℝ)/8) ∧ Real.exp ((-683298462377/1000000000000 : ℝ)/8) ≤ (28691676646456611/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683298462377/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0013_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009897376417/500000000000 : ℝ) ≤ 4*Real.exp (27/256 : ℝ)*Real.exp (-mu (radius 7 (55/512 : ℝ))) ∧ (2019/1000 : ℝ) < (1009897376417/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (55/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0013_exp_radius
  have hrNumeric : (984771167417/1000000000000 : ℝ) ≤ Real.exp (-55/3584 : ℝ) ∧ Real.exp (-55/3584 : ℝ) ≤ (492385583709/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984771167417/1000000000000 : ℝ) ≤ (radius 7 (55/512 : ℝ)) ∧ (radius 7 (55/512 : ℝ)) ≤ (492385583709/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (55/512 : ℝ)) (984771167417/1000000000000 : ℝ) (492385583709/500000000000 : ℝ) (8692776861/50000000000 : ℝ) (173855537227/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (55/512 : ℝ)) (984771167417/1000000000000 : ℝ) (492385583709/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (55/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984771167417/1000000000000 : ℝ) (492385583709/500000000000 : ℝ) (248096395927/250000000000 : ℝ) (992385583709/1000000000000 : ℝ) (992356371177/1000000000000 : ℝ) (992356371179/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (55/512 : ℝ)) 1 (248096395927/250000000000 : ℝ) (992385583709/1000000000000 : ℝ) (992356371177/1000000000000 : ℝ) (992356371179/1000000000000 : ℝ) (496185488721/500000000000 : ℝ) (248092744361/250000000000 : ℝ) (198474195467/200000000000 : ℝ) (992370977337/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (55/512 : ℝ)) 2 (496185488721/500000000000 : ℝ) (248092744361/250000000000 : ℝ) (198474195467/200000000000 : ℝ) (992370977337/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (55/512 : ℝ)) 3 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (55/512 : ℝ)) 4 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (55/512 : ℝ)) 5 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (55/512 : ℝ)) 6 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (55/512 : ℝ)) 7 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (55/512 : ℝ))) (8692776861/50000000000 : ℝ) (173855537227/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8692776861/50000000000 : ℝ) (173855537227/1000000000000 : ℝ) (58692776861/100000000000 : ℝ) (293463884307/500000000000 : ℝ) (26059992177/62500000000 : ℝ) (416959874841/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 1 (58692776861/100000000000 : ℝ) (293463884307/500000000000 : ℝ) (26059992177/62500000000 : ℝ) (416959874841/1000000000000 : ℝ) (501943821721/1000000000000 : ℝ) (15685744429/31250000000 : ℝ) (247348604673/500000000000 : ℝ) (247348604677/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 2 (501943821721/1000000000000 : ℝ) (15685744429/31250000000 : ℝ) (247348604673/500000000000 : ℝ) (247348604677/500000000000 : ℝ) (498320515533/1000000000000 : ℝ) (498320515541/1000000000000 : ℝ) (99661468553/200000000000 : ℝ) (498307342773/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 3 (498320515533/1000000000000 : ℝ) (498320515541/1000000000000 : ℝ) (99661468553/200000000000 : ℝ) (498307342773/1000000000000 : ℝ) (498313929149/1000000000000 : ℝ) (498313929157/1000000000000 : ℝ) (99662785821/200000000000 : ℝ) (249156964557/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 4 (498313929149/1000000000000 : ℝ) (498313929157/1000000000000 : ℝ) (99662785821/200000000000 : ℝ) (249156964557/500000000000 : ℝ) (498313929127/1000000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 5 (498313929127/1000000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 6 (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (55/512 : ℝ))) 7 (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (55/512 : ℝ)) hmem 8 (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (55/512 : ℝ))) hcmem 8 (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (55/512 : ℝ)) (248092744347/250000000000 : ℝ) (992370977391/1000000000000 : ℝ) (249156964563/500000000000 : ℝ) (31144620571/62500000000 : ℝ) (394383606179/500000000000 : ℝ) (788767212377/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0013_exp_lower
  have heNumeric : (1009897376417/500000000000 : ℝ)/4 ≤ Real.exp (-683298462377/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009897376417/500000000000 : ℝ)/4 ≤ Real.exp ((27/256 : ℝ)-(788767212377/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (27/256 : ℝ) (55/512 : ℝ) (788767212377/1000000000000 : ℝ) (1009897376417/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0014; no trusted numerical premise.
theorem cover7_leaf0014_exp_radius : (62378048819217217/62500000000000000 : ℝ) ≤ Real.exp ((-1/64 : ℝ)/8) ∧ Real.exp ((-1/64 : ℝ)/8) ≤ (998048781107475473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/64 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0014_exp_lower : (459048171894101523/500000000000000000 : ℝ) ≤ Real.exp ((-136724710733/200000000000 : ℝ)/8) ∧ Real.exp ((-136724710733/200000000000 : ℝ)/8) ≤ (918096343788203047/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136724710733/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0014_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (3230621187/1600000000 : ℝ) ≤ 4*Real.exp (55/512 : ℝ)*Real.exp (-mu (radius 7 (7/64 : ℝ))) ∧ (2019/1000 : ℝ) < (3230621187/1600000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (7/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0014_exp_radius
  have hrNumeric : (196899287401/200000000000 : ℝ) ≤ Real.exp (-1/64 : ℝ) ∧ Real.exp (-1/64 : ℝ) ≤ (492248218503/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196899287401/200000000000 : ℝ) ≤ (radius 7 (7/64 : ℝ)) ∧ (radius 7 (7/64 : ℝ)) ≤ (492248218503/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (7/64 : ℝ)) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (7/64 : ℝ)) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (7/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (496124109251/500000000000 : ℝ) (992248218503/1000000000000 : ℝ) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (7/64 : ℝ)) 1 (496124109251/500000000000 : ℝ) (992248218503/1000000000000 : ℝ) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ) (992233078381/1000000000000 : ℝ) (496116539191/500000000000 : ℝ) (198446615653/200000000000 : ℝ) (992233078267/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (7/64 : ℝ)) 2 (992233078381/1000000000000 : ℝ) (496116539191/500000000000 : ℝ) (198446615653/200000000000 : ℝ) (992233078267/1000000000000 : ℝ) (992233078323/1000000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (7/64 : ℝ)) 3 (992233078323/1000000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (7/64 : ℝ)) 4 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (7/64 : ℝ)) 5 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (7/64 : ℝ)) 6 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (7/64 : ℝ)) 7 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (7/64 : ℝ))) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ) (587702288343/1000000000000 : ℝ) (293851144173/500000000000 : ℝ) (52351661967/125000000000 : ℝ) (83762659149/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 1 (587702288343/1000000000000 : ℝ) (293851144173/500000000000 : ℝ) (52351661967/125000000000 : ℝ) (83762659149/200000000000 : ℝ) (503257792039/1000000000000 : ℝ) (251628896023/500000000000 : ℝ) (99224499453/200000000000 : ℝ) (62015312159/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 2 (503257792039/1000000000000 : ℝ) (251628896023/500000000000 : ℝ) (99224499453/200000000000 : ℝ) (62015312159/125000000000 : ℝ) (124922536163/250000000000 : ℝ) (499690144659/1000000000000 : ℝ) (499677408489/1000000000000 : ℝ) (499677408497/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 3 (124922536163/250000000000 : ℝ) (499690144659/1000000000000 : ℝ) (499677408489/1000000000000 : ℝ) (499677408497/1000000000000 : ℝ) (49968377657/100000000000 : ℝ) (249841888289/500000000000 : ℝ) (499683776529/1000000000000 : ℝ) (249841888269/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 4 (49968377657/100000000000 : ℝ) (249841888289/500000000000 : ℝ) (499683776529/1000000000000 : ℝ) (249841888269/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 5 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 6 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (7/64 : ℝ))) 7 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (7/64 : ℝ)) hmem 8 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (7/64 : ℝ))) hcmem 8 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (7/64 : ℝ)) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (791045428647/1000000000000 : ℝ) (158209085733/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0014_exp_lower
  have heNumeric : (3230621187/1600000000 : ℝ)/4 ≤ Real.exp (-136724710733/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (3230621187/1600000000 : ℝ)/4 ≤ Real.exp ((55/512 : ℝ)-(158209085733/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (55/512 : ℝ) (7/64 : ℝ) (158209085733/200000000000 : ℝ) (3230621187/1600000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0015; no trusted numerical premise.
theorem cover7_leaf0015_exp_radius : (998031376669716277/1000000000000000000 : ℝ) ≤ Real.exp ((-113/7168 : ℝ)/8) ∧ Real.exp ((-113/7168 : ℝ)/8) ≤ (499015688334858139/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-113/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0015_exp_lower : (918190955480276803/1000000000000000000 : ℝ) ≤ Real.exp ((-6827991799/10000000000 : ℝ)/8) ∧ Real.exp ((-6827991799/10000000000 : ℝ)/8) ≤ (229547738870069201/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6827991799/10000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0015_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2020803452753/1000000000000 : ℝ) ≤ 4*Real.exp (7/64 : ℝ)*Real.exp (-mu (radius 7 (113/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2020803452753/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (113/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0015_exp_radius
  have hrNumeric : (492179550271/500000000000 : ℝ) ≤ Real.exp (-113/7168 : ℝ) ∧ Real.exp (-113/7168 : ℝ) ≤ (984359100543/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492179550271/500000000000 : ℝ) ≤ (radius 7 (113/1024 : ℝ)) ∧ (radius 7 (113/1024 : ℝ)) ≤ (984359100543/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (113/1024 : ℝ)) (492179550271/500000000000 : ℝ) (984359100543/1000000000000 : ℝ) (176173667663/1000000000000 : ℝ) (17617366767/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (113/1024 : ℝ)) (492179550271/500000000000 : ℝ) (984359100543/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (113/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492179550271/500000000000 : ℝ) (984359100543/1000000000000 : ℝ) (992179550271/1000000000000 : ℝ) (15502805473/15625000000 : ℝ) (992148729043/1000000000000 : ℝ) (248037182261/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (113/1024 : ℝ)) 1 (992179550271/1000000000000 : ℝ) (15502805473/15625000000 : ℝ) (992148729043/1000000000000 : ℝ) (248037182261/250000000000 : ℝ) (992164139657/1000000000000 : ℝ) (496082069829/500000000000 : ℝ) (992164139537/1000000000000 : ℝ) (992164139539/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (113/1024 : ℝ)) 2 (992164139657/1000000000000 : ℝ) (496082069829/500000000000 : ℝ) (992164139537/1000000000000 : ℝ) (992164139539/1000000000000 : ℝ) (992164139597/1000000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (113/1024 : ℝ)) 3 (992164139597/1000000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (113/1024 : ℝ)) 4 (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (113/1024 : ℝ)) 5 (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (113/1024 : ℝ)) 6 (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (113/1024 : ℝ)) 7 (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (113/1024 : ℝ))) (176173667663/1000000000000 : ℝ) (17617366767/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176173667663/1000000000000 : ℝ) (17617366767/100000000000 : ℝ) (588086833831/1000000000000 : ℝ) (117617366767/200000000000 : ℝ) (419730470257/1000000000000 : ℝ) (419730470267/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 1 (588086833831/1000000000000 : ℝ) (117617366767/200000000000 : ℝ) (419730470257/1000000000000 : ℝ) (419730470267/1000000000000 : ℝ) (125977163011/250000000000 : ℝ) (503908652051/1000000000000 : ℝ) (31051743819/62500000000 : ℝ) (496827901113/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 2 (125977163011/250000000000 : ℝ) (503908652051/1000000000000 : ℝ) (31051743819/62500000000 : ℝ) (496827901113/1000000000000 : ℝ) (250184138287/500000000000 : ℝ) (250184138291/500000000000 : ℝ) (62544468923/125000000000 : ℝ) (500355751393/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 3 (250184138287/500000000000 : ℝ) (250184138291/500000000000 : ℝ) (62544468923/125000000000 : ℝ) (500355751393/1000000000000 : ℝ) (500362013979/1000000000000 : ℝ) (125090503497/250000000000 : ℝ) (500362013939/1000000000000 : ℝ) (500362013949/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 4 (500362013979/1000000000000 : ℝ) (125090503497/250000000000 : ℝ) (500362013939/1000000000000 : ℝ) (500362013949/1000000000000 : ℝ) (500362013959/1000000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 5 (500362013959/1000000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 6 (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (113/1024 : ℝ))) 7 (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (113/1024 : ℝ)) hmem 8 (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (113/1024 : ℝ))) hcmem 8 (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (113/1024 : ℝ)) (248041034899/250000000000 : ℝ) (992164139599/1000000000000 : ℝ) (250181006979/500000000000 : ℝ) (500362013969/1000000000000 : ℝ) (792174179879/1000000000000 : ℝ) (7921741799/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0015_exp_lower
  have heNumeric : (2020803452753/1000000000000 : ℝ)/4 ≤ Real.exp (-6827991799/10000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2020803452753/1000000000000 : ℝ)/4 ≤ Real.exp ((7/64 : ℝ)-(7921741799/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (7/64 : ℝ) (113/1024 : ℝ) (7921741799/10000000000 : ℝ) (2020803452753/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0016; no trusted numerical premise.
theorem cover7_leaf0016_exp_radius : (998013972535463743/1000000000000000000 : ℝ) ≤ Real.exp ((-57/3584 : ℝ)/8) ∧ Real.exp ((-57/3584 : ℝ)/8) ≤ (15593968320866621/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-57/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0016_exp_lower : (918174264439446547/1000000000000000000 : ℝ) ≤ Real.exp ((-136588921333/200000000000 : ℝ)/8) ∧ Real.exp ((-136588921333/200000000000 : ℝ)/8) ≤ (229543566109861637/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136588921333/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0016_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505127398803/250000000000 : ℝ) ≤ 4*Real.exp (113/1024 : ℝ)*Real.exp (-mu (radius 7 (57/512 : ℝ))) ∧ (2019/1000 : ℝ) < (505127398803/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (57/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0016_exp_radius
  have hrNumeric : (984221783237/1000000000000 : ℝ) ≤ Real.exp (-57/3584 : ℝ) ∧ Real.exp (-57/3584 : ℝ) ≤ (492110891619/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984221783237/1000000000000 : ℝ) ≤ (radius 7 (57/512 : ℝ)) ∧ (radius 7 (57/512 : ℝ)) ≤ (492110891619/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (57/512 : ℝ)) (984221783237/1000000000000 : ℝ) (492110891619/500000000000 : ℝ) (22117400319/125000000000 : ℝ) (88469601279/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (57/512 : ℝ)) (984221783237/1000000000000 : ℝ) (492110891619/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (57/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984221783237/1000000000000 : ℝ) (492110891619/500000000000 : ℝ) (496055445809/500000000000 : ℝ) (992110891619/1000000000000 : ℝ) (992079524653/1000000000000 : ℝ) (198415904931/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (57/512 : ℝ)) 1 (496055445809/500000000000 : ℝ) (992110891619/1000000000000 : ℝ) (992079524653/1000000000000 : ℝ) (198415904931/200000000000 : ℝ) (198419041627/200000000000 : ℝ) (992095208137/1000000000000 : ℝ) (992095208011/1000000000000 : ℝ) (496047604007/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (57/512 : ℝ)) 2 (198419041627/200000000000 : ℝ) (992095208137/1000000000000 : ℝ) (992095208011/1000000000000 : ℝ) (496047604007/500000000000 : ℝ) (992095208073/1000000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (57/512 : ℝ)) 3 (992095208073/1000000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (57/512 : ℝ)) 4 (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (57/512 : ℝ)) 5 (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (57/512 : ℝ)) 6 (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (57/512 : ℝ)) 7 (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (57/512 : ℝ))) (22117400319/125000000000 : ℝ) (88469601279/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22117400319/125000000000 : ℝ) (88469601279/500000000000 : ℝ) (147117400319/250000000000 : ℝ) (588469601279/1000000000000 : ℝ) (420641418017/1000000000000 : ℝ) (16825656721/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 1 (147117400319/250000000000 : ℝ) (588469601279/1000000000000 : ℝ) (420641418017/1000000000000 : ℝ) (16825656721/40000000000 : ℝ) (252277754823/500000000000 : ℝ) (126138877413/250000000000 : ℝ) (497528579621/1000000000000 : ℝ) (124382144907/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 2 (252277754823/500000000000 : ℝ) (126138877413/250000000000 : ℝ) (497528579621/1000000000000 : ℝ) (124382144907/250000000000 : ℝ) (501042044633/1000000000000 : ℝ) (3131512779/6250000000 : ℝ) (501029725719/1000000000000 : ℝ) (250514862863/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 3 (501042044633/1000000000000 : ℝ) (3131512779/6250000000 : ℝ) (501029725719/1000000000000 : ℝ) (250514862863/500000000000 : ℝ) (62629485647/125000000000 : ℝ) (501035885183/1000000000000 : ℝ) (250517942569/500000000000 : ℝ) (250517942573/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 4 (62629485647/125000000000 : ℝ) (501035885183/1000000000000 : ℝ) (250517942569/500000000000 : ℝ) (250517942573/500000000000 : ℝ) (501035885157/1000000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 5 (501035885157/1000000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 6 (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (57/512 : ℝ))) 7 (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (57/512 : ℝ)) hmem 8 (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (57/512 : ℝ))) hcmem 8 (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (57/512 : ℝ)) (124011901009/125000000000 : ℝ) (248023802019/250000000000 : ℝ) (125258971289/250000000000 : ℝ) (100207177033/200000000000 : ℝ) (396648084573/500000000000 : ℝ) (158659233833/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0016_exp_lower
  have heNumeric : (505127398803/250000000000 : ℝ)/4 ≤ Real.exp (-136588921333/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505127398803/250000000000 : ℝ)/4 ≤ Real.exp ((113/1024 : ℝ)-(158659233833/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (113/1024 : ℝ) (57/512 : ℝ) (158659233833/200000000000 : ℝ) (505127398803/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0017; no trusted numerical premise.
theorem cover7_leaf0017_exp_radius : (498998284352356289/500000000000000000 : ℝ) ≤ Real.exp ((-115/7168 : ℝ)/8) ∧ Real.exp ((-115/7168 : ℝ)/8) ≤ (997996568704712579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-115/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0017_exp_lower : (183631667573099911/200000000000000000 : ℝ) ≤ Real.exp ((-683083375199/1000000000000 : ℝ)/8) ∧ Real.exp ((-683083375199/1000000000000 : ℝ)/8) ≤ (229539584466374889/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683083375199/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0017_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2020229231511/1000000000000 : ℝ) ≤ 4*Real.exp (57/512 : ℝ)*Real.exp (-mu (radius 7 (115/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2020229231511/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (115/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0017_exp_radius
  have hrNumeric : (30752640159/31250000000 : ℝ) ≤ Real.exp (-115/7168 : ℝ) ∧ Real.exp (-115/7168 : ℝ) ≤ (984084485089/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30752640159/31250000000 : ℝ) ≤ (radius 7 (115/1024 : ℝ)) ∧ (radius 7 (115/1024 : ℝ)) ≤ (984084485089/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (115/1024 : ℝ)) (30752640159/31250000000 : ℝ) (984084485089/1000000000000 : ℝ) (35540245473/200000000000 : ℝ) (177701227371/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (115/1024 : ℝ)) (30752640159/31250000000 : ℝ) (984084485089/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (115/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30752640159/31250000000 : ℝ) (984084485089/1000000000000 : ℝ) (62002640159/62500000000 : ℝ) (198408448509/200000000000 : ℝ) (992010325091/1000000000000 : ℝ) (248002581273/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (115/1024 : ℝ)) 1 (62002640159/62500000000 : ℝ) (198408448509/200000000000 : ℝ) (992010325091/1000000000000 : ℝ) (248002581273/250000000000 : ℝ) (992026283817/1000000000000 : ℝ) (992026283819/1000000000000 : ℝ) (992026283689/1000000000000 : ℝ) (992026283691/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (115/1024 : ℝ)) 2 (992026283817/1000000000000 : ℝ) (992026283819/1000000000000 : ℝ) (992026283689/1000000000000 : ℝ) (992026283691/1000000000000 : ℝ) (992026283753/1000000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (115/1024 : ℝ)) 3 (992026283753/1000000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (115/1024 : ℝ)) 4 (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (115/1024 : ℝ)) 5 (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (115/1024 : ℝ)) 6 (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (115/1024 : ℝ)) 7 (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (115/1024 : ℝ))) (35540245473/200000000000 : ℝ) (177701227371/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35540245473/200000000000 : ℝ) (177701227371/1000000000000 : ℝ) (294425306841/500000000000 : ℝ) (294425306843/500000000000 : ℝ) (210773116979/500000000000 : ℝ) (421546233967/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 1 (294425306841/500000000000 : ℝ) (294425306843/500000000000 : ℝ) (210773116979/500000000000 : ℝ) (421546233967/1000000000000 : ℝ) (25259921191/50000000000 : ℝ) (505198423827/1000000000000 : ℝ) (498224606539/1000000000000 : ℝ) (498224606547/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 2 (25259921191/50000000000 : ℝ) (505198423827/1000000000000 : ℝ) (498224606539/1000000000000 : ℝ) (498224606547/1000000000000 : ℝ) (501711515179/1000000000000 : ℝ) (501711515187/1000000000000 : ℝ) (250849698989/500000000000 : ℝ) (250849698993/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 3 (501711515179/1000000000000 : ℝ) (501711515187/1000000000000 : ℝ) (250849698989/500000000000 : ℝ) (250849698993/500000000000 : ℝ) (250852728289/500000000000 : ℝ) (501705456587/1000000000000 : ℝ) (501705456541/1000000000000 : ℝ) (10034109131/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 4 (250852728289/500000000000 : ℝ) (501705456587/1000000000000 : ℝ) (501705456541/1000000000000 : ℝ) (10034109131/20000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 5 (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 6 (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (115/1024 : ℝ))) 7 (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (115/1024 : ℝ)) hmem 8 (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (115/1024 : ℝ))) hcmem 8 (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (115/1024 : ℝ)) (124003285469/125000000000 : ℝ) (198405256751/200000000000 : ℝ) (501705456559/1000000000000 : ℝ) (501705456569/1000000000000 : ℝ) (39720575009/50000000000 : ℝ) (794411500199/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0017_exp_lower
  have heNumeric : (2020229231511/1000000000000 : ℝ)/4 ≤ Real.exp (-683083375199/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2020229231511/1000000000000 : ℝ)/4 ≤ Real.exp ((57/512 : ℝ)-(794411500199/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (57/512 : ℝ) (115/1024 : ℝ) (794411500199/1000000000000 : ℝ) (2020229231511/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0018; no trusted numerical premise.
theorem cover7_leaf0018_exp_radius : (99797916517745749/100000000000000000 : ℝ) ≤ Real.exp ((-29/1792 : ℝ)/8) ∧ Real.exp ((-29/1792 : ℝ)/8) ≤ (997979165177457491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-29/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0018_exp_lower : (183628632819637187/200000000000000000 : ℝ) ≤ Real.exp ((-341607793377/500000000000 : ℝ)/8) ∧ Real.exp ((-341607793377/500000000000 : ℝ)/8) ≤ (57383947756136621/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341607793377/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0018_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019962151519/1000000000000 : ℝ) ≤ 4*Real.exp (115/1024 : ℝ)*Real.exp (-mu (radius 7 (29/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019962151519/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (29/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0018_exp_radius
  have hrNumeric : (245986801523/250000000000 : ℝ) ≤ Real.exp (-29/1792 : ℝ) ∧ Real.exp (-29/1792 : ℝ) ≤ (983947206093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245986801523/250000000000 : ℝ) ≤ (radius 7 (29/256 : ℝ)) ∧ (radius 7 (29/256 : ℝ)) ≤ (983947206093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (29/256 : ℝ)) (245986801523/250000000000 : ℝ) (983947206093/1000000000000 : ℝ) (22307473391/125000000000 : ℝ) (89229893567/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (29/256 : ℝ)) (245986801523/250000000000 : ℝ) (983947206093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (29/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245986801523/250000000000 : ℝ) (983947206093/1000000000000 : ℝ) (495986801523/500000000000 : ℝ) (991973603047/1000000000000 : ℝ) (247985282589/250000000000 : ℝ) (991941130357/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (29/256 : ℝ)) 1 (495986801523/500000000000 : ℝ) (991973603047/1000000000000 : ℝ) (247985282589/250000000000 : ℝ) (991941130357/1000000000000 : ℝ) (991957366701/1000000000000 : ℝ) (495978683351/500000000000 : ℝ) (123994670821/125000000000 : ℝ) (99195736657/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (29/256 : ℝ)) 2 (991957366701/1000000000000 : ℝ) (495978683351/500000000000 : ℝ) (123994670821/125000000000 : ℝ) (99195736657/100000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (29/256 : ℝ)) 3 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (29/256 : ℝ)) 4 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (29/256 : ℝ)) 5 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (29/256 : ℝ)) 6 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (29/256 : ℝ)) 7 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (29/256 : ℝ))) (22307473391/125000000000 : ℝ) (89229893567/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22307473391/125000000000 : ℝ) (89229893567/500000000000 : ℝ) (147307473391/250000000000 : ℝ) (589229893567/1000000000000 : ℝ) (211222505387/500000000000 : ℝ) (211222505391/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 1 (147307473391/250000000000 : ℝ) (589229893567/1000000000000 : ℝ) (211222505387/500000000000 : ℝ) (211222505391/500000000000 : ℝ) (505837452169/1000000000000 : ℝ) (20233498087/40000000000 : ℝ) (99783210759/200000000000 : ℝ) (249458026901/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 2 (505837452169/1000000000000 : ℝ) (20233498087/40000000000 : ℝ) (99783210759/200000000000 : ℝ) (249458026901/500000000000 : ℝ) (251188376491/500000000000 : ℝ) (502376752989/1000000000000 : ℝ) (251182416531/500000000000 : ℝ) (502364833069/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 3 (251188376491/500000000000 : ℝ) (502376752989/1000000000000 : ℝ) (251182416531/500000000000 : ℝ) (502364833069/1000000000000 : ℝ) (251185396511/500000000000 : ℝ) (502370793029/1000000000000 : ℝ) (251185396493/500000000000 : ℝ) (251185396497/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 4 (251185396511/500000000000 : ℝ) (502370793029/1000000000000 : ℝ) (251185396493/500000000000 : ℝ) (251185396497/500000000000 : ℝ) (125592698251/250000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 5 (125592698251/250000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 6 (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (29/256 : ℝ))) 7 (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (29/256 : ℝ)) hmem 8 (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (29/256 : ℝ))) hcmem 8 (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (29/256 : ℝ)) (495978683317/500000000000 : ℝ) (247989341659/250000000000 : ℝ) (502370793003/1000000000000 : ℝ) (125592698253/250000000000 : ℝ) (795520274237/1000000000000 : ℝ) (397760137127/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0018_exp_lower
  have heNumeric : (2019962151519/1000000000000 : ℝ)/4 ≤ Real.exp (-341607793377/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019962151519/1000000000000 : ℝ)/4 ≤ Real.exp ((115/1024 : ℝ)-(397760137127/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (115/1024 : ℝ) (29/256 : ℝ) (397760137127/500000000000 : ℝ) (2019962151519/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0019; no trusted numerical premise.
theorem cover7_leaf0019_exp_radius : (199592352390738637/200000000000000000 : ℝ) ≤ Real.exp ((-117/7168 : ℝ)/8) ∧ Real.exp ((-117/7168 : ℝ)/8) ≤ (498980880976846593/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-117/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0019_exp_lower : (918128731755563037/1000000000000000000 : ℝ) ≤ Real.exp ((-34167067009/50000000000 : ℝ)/8) ∧ Real.exp ((-34167067009/50000000000 : ℝ)/8) ≤ (459064365877781519/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-34167067009/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0019_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019708150329/1000000000000 : ℝ) ≤ 4*Real.exp (29/256 : ℝ)*Real.exp (-mu (radius 7 (117/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019708150329/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (117/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0019_exp_radius
  have hrNumeric : (491904973123/500000000000 : ℝ) ≤ Real.exp (-117/7168 : ℝ) ∧ Real.exp (-117/7168 : ℝ) ≤ (983809946247/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491904973123/500000000000 : ℝ) ≤ (radius 7 (117/1024 : ℝ)) ∧ (radius 7 (117/1024 : ℝ)) ≤ (983809946247/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (117/1024 : ℝ)) (491904973123/500000000000 : ℝ) (983809946247/1000000000000 : ℝ) (1792149259/10000000000 : ℝ) (89607462953/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (117/1024 : ℝ)) (491904973123/500000000000 : ℝ) (983809946247/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (117/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491904973123/500000000000 : ℝ) (983809946247/1000000000000 : ℝ) (991904973123/1000000000000 : ℝ) (247976243281/250000000000 : ℝ) (495935970223/500000000000 : ℝ) (30995998139/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (117/1024 : ℝ)) 1 (991904973123/1000000000000 : ℝ) (247976243281/250000000000 : ℝ) (495935970223/500000000000 : ℝ) (30995998139/31250000000 : ℝ) (61993028549/62500000000 : ℝ) (495944228393/500000000000 : ℝ) (495944228323/500000000000 : ℝ) (991888456649/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (117/1024 : ℝ)) 2 (61993028549/62500000000 : ℝ) (495944228393/500000000000 : ℝ) (495944228323/500000000000 : ℝ) (991888456649/1000000000000 : ℝ) (198377691343/200000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (117/1024 : ℝ)) 3 (198377691343/200000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (117/1024 : ℝ)) 4 (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (117/1024 : ℝ)) 5 (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (117/1024 : ℝ)) 6 (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (117/1024 : ℝ)) 7 (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (117/1024 : ℝ))) (1792149259/10000000000 : ℝ) (89607462953/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1792149259/10000000000 : ℝ) (89607462953/500000000000 : ℝ) (11792149259/20000000000 : ℝ) (589607462953/1000000000000 : ℝ) (84667567793/200000000000 : ℝ) (423337838973/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 1 (11792149259/20000000000 : ℝ) (589607462953/1000000000000 : ℝ) (84667567793/200000000000 : ℝ) (423337838973/1000000000000 : ℝ) (506472650957/1000000000000 : ℝ) (506472650963/1000000000000 : ℝ) (499602991587/1000000000000 : ℝ) (249801495797/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 2 (506472650957/1000000000000 : ℝ) (506472650963/1000000000000 : ℝ) (499602991587/1000000000000 : ℝ) (249801495797/500000000000 : ℝ) (62879727659/125000000000 : ℝ) (503037821279/1000000000000 : ℝ) (62878261791/125000000000 : ℝ) (100605218867/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 3 (62879727659/125000000000 : ℝ) (503037821279/1000000000000 : ℝ) (62878261791/125000000000 : ℝ) (100605218867/200000000000 : ℝ) (2515159789/5000000000 : ℝ) (503031957807/1000000000000 : ℝ) (100606391553/200000000000 : ℝ) (503031957773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 4 (2515159789/5000000000 : ℝ) (503031957807/1000000000000 : ℝ) (100606391553/200000000000 : ℝ) (503031957773/1000000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 5 (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 6 (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (117/1024 : ℝ))) 7 (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (117/1024 : ℝ)) hmem 8 (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (117/1024 : ℝ))) hcmem 8 (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (117/1024 : ℝ)) (495944228357/500000000000 : ℝ) (495944228359/500000000000 : ℝ) (251515978891/500000000000 : ℝ) (50303195779/100000000000 : ℝ) (796622590163/1000000000000 : ℝ) (39831129509/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0019_exp_lower
  have heNumeric : (2019708150329/1000000000000 : ℝ)/4 ≤ Real.exp (-34167067009/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019708150329/1000000000000 : ℝ)/4 ≤ Real.exp ((29/256 : ℝ)-(39831129509/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (29/256 : ℝ) (117/1024 : ℝ) (39831129509/50000000000 : ℝ) (2019708150329/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0020; no trusted numerical premise.
theorem cover7_leaf0020_exp_radius : (249486089758353593/250000000000000000 : ℝ) ≤ Real.exp ((-59/3584 : ℝ)/8) ∧ Real.exp ((-59/3584 : ℝ)/8) ≤ (997944359033414373/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-59/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0020_exp_lower : (229528757431662509/250000000000000000 : ℝ) ≤ Real.exp ((-170865182997/250000000000 : ℝ)/8) ∧ Real.exp ((-170865182997/250000000000 : ℝ)/8) ≤ (918115029726650037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170865182997/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0020_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403893405623/200000000000 : ℝ) ≤ 4*Real.exp (117/1024 : ℝ)*Real.exp (-mu (radius 7 (59/512 : ℝ))) ∧ (2019/1000 : ℝ) < (403893405623/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (59/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0020_exp_radius
  have hrNumeric : (245918176387/250000000000 : ℝ) ≤ Real.exp (-59/3584 : ℝ) ∧ Real.exp (-59/3584 : ℝ) ≤ (983672705549/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245918176387/250000000000 : ℝ) ≤ (radius 7 (59/512 : ℝ)) ∧ (radius 7 (59/512 : ℝ)) ≤ (983672705549/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (59/512 : ℝ)) (245918176387/250000000000 : ℝ) (983672705549/1000000000000 : ℝ) (449916717/2500000000 : ℝ) (89983343403/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (59/512 : ℝ)) (245918176387/250000000000 : ℝ) (983672705549/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (59/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245918176387/250000000000 : ℝ) (983672705549/1000000000000 : ℝ) (495918176387/500000000000 : ℝ) (39673454111/40000000000 : ℝ) (247950688841/250000000000 : ℝ) (198360551073/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (59/512 : ℝ)) 1 (495918176387/500000000000 : ℝ) (39673454111/40000000000 : ℝ) (247950688841/250000000000 : ℝ) (198360551073/200000000000 : ℝ) (991819554069/1000000000000 : ℝ) (99181955407/100000000000 : ℝ) (495909776963/500000000000 : ℝ) (123977444241/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (59/512 : ℝ)) 2 (991819554069/1000000000000 : ℝ) (99181955407/100000000000 : ℝ) (495909776963/500000000000 : ℝ) (123977444241/125000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (59/512 : ℝ)) 3 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (59/512 : ℝ)) 4 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (59/512 : ℝ)) 5 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (59/512 : ℝ)) 6 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (59/512 : ℝ)) 7 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (59/512 : ℝ))) (449916717/2500000000 : ℝ) (89983343403/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (449916717/2500000000 : ℝ) (89983343403/500000000000 : ℝ) (2949916717/5000000000 : ℝ) (589983343403/1000000000000 : ℝ) (207141019/488281250 : ℝ) (10605620173/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 1 (2949916717/5000000000 : ℝ) (589983343403/1000000000000 : ℝ) (207141019/488281250 : ℝ) (10605620173/25000000000 : ℝ) (126776018789/250000000000 : ℝ) (253552037581/500000000000 : ℝ) (500285488431/1000000000000 : ℝ) (250142744219/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 2 (126776018789/250000000000 : ℝ) (253552037581/500000000000 : ℝ) (500285488431/1000000000000 : ℝ) (250142744219/500000000000 : ℝ) (503694781793/1000000000000 : ℝ) (2518473909/5000000000 : ℝ) (503683243641/1000000000000 : ℝ) (3935025341/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 3 (503694781793/1000000000000 : ℝ) (2518473909/5000000000 : ℝ) (503683243641/1000000000000 : ℝ) (3935025341/7812500000 : ℝ) (503689012717/1000000000000 : ℝ) (125922253181/250000000000 : ℝ) (503689012683/1000000000000 : ℝ) (503689012691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 4 (503689012717/1000000000000 : ℝ) (125922253181/250000000000 : ℝ) (503689012683/1000000000000 : ℝ) (503689012691/1000000000000 : ℝ) (5036890127/10000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 5 (5036890127/10000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 6 (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (59/512 : ℝ))) 7 (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (59/512 : ℝ)) hmem 8 (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (59/512 : ℝ))) hcmem 8 (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (59/512 : ℝ)) (991819553997/1000000000000 : ℝ) (991819553999/1000000000000 : ℝ) (503689012699/1000000000000 : ℝ) (125922253177/250000000000 : ℝ) (797718544471/1000000000000 : ℝ) (99714818061/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0020_exp_lower
  have heNumeric : (403893405623/200000000000 : ℝ)/4 ≤ Real.exp (-170865182997/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403893405623/200000000000 : ℝ)/4 ≤ Real.exp ((117/1024 : ℝ)-(99714818061/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (117/1024 : ℝ) (59/512 : ℝ) (99714818061/125000000000 : ℝ) (403893405623/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0021; no trusted numerical premise.
theorem cover7_leaf0021_exp_radius : (498963478208307879/500000000000000000 : ℝ) ≤ Real.exp ((-17/1024 : ℝ)/8) ∧ Real.exp ((-17/1024 : ℝ)/8) ≤ (997926956416615759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0021_exp_lower : (918102047160644967/1000000000000000000 : ℝ) ≤ Real.exp ((-683573856443/1000000000000 : ℝ)/8) ∧ Real.exp ((-683573856443/1000000000000 : ℝ)/8) ≤ (114762755895080621/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683573856443/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0021_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201923858993/100000000000 : ℝ) ≤ 4*Real.exp (59/512 : ℝ)*Real.exp (-mu (radius 7 (119/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (201923858993/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (119/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0021_exp_radius
  have hrNumeric : (196707096799/200000000000 : ℝ) ≤ Real.exp (-17/1024 : ℝ) ∧ Real.exp (-17/1024 : ℝ) ≤ (245883870999/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196707096799/200000000000 : ℝ) ≤ (radius 7 (119/1024 : ℝ)) ∧ (radius 7 (119/1024 : ℝ)) ≤ (245883870999/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (119/1024 : ℝ)) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (119/1024 : ℝ)) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (119/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196707096799/200000000000 : ℝ) (245883870999/250000000000 : ℝ) (991767741997/1000000000000 : ℝ) (495883870999/500000000000 : ℝ) (991733575107/1000000000000 : ℝ) (247933393777/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (119/1024 : ℝ)) 1 (991767741997/1000000000000 : ℝ) (495883870999/500000000000 : ℝ) (991733575107/1000000000000 : ℝ) (247933393777/250000000000 : ℝ) (123968832319/125000000000 : ℝ) (991750658553/1000000000000 : ℝ) (247937664601/250000000000 : ℝ) (495875329203/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (119/1024 : ℝ)) 2 (123968832319/125000000000 : ℝ) (991750658553/1000000000000 : ℝ) (247937664601/250000000000 : ℝ) (495875329203/500000000000 : ℝ) (495875329239/500000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (119/1024 : ℝ)) 3 (495875329239/500000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (119/1024 : ℝ)) 4 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (119/1024 : ℝ)) 5 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (119/1024 : ℝ)) 6 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (119/1024 : ℝ)) 7 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (119/1024 : ℝ))) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180715112043/1000000000000 : ℝ) (180715112049/1000000000000 : ℝ) (590357556021/1000000000000 : ℝ) (23614302241/40000000000 : ℝ) (425106000949/1000000000000 : ℝ) (425106000957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 1 (590357556021/1000000000000 : ℝ) (23614302241/40000000000 : ℝ) (425106000949/1000000000000 : ℝ) (425106000957/1000000000000 : ℝ) (101546355697/200000000000 : ℝ) (507731778491/1000000000000 : ℝ) (500963611223/1000000000000 : ℝ) (50096361123/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 2 (101546355697/200000000000 : ℝ) (507731778491/1000000000000 : ℝ) (500963611223/1000000000000 : ℝ) (50096361123/100000000000 : ℝ) (252173847427/500000000000 : ℝ) (504347694861/1000000000000 : ℝ) (20173453657/40000000000 : ℝ) (504336341433/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 3 (252173847427/500000000000 : ℝ) (504347694861/1000000000000 : ℝ) (20173453657/40000000000 : ℝ) (504336341433/1000000000000 : ℝ) (504342018139/1000000000000 : ℝ) (504342018147/1000000000000 : ℝ) (504342018107/1000000000000 : ℝ) (126085504529/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 4 (504342018139/1000000000000 : ℝ) (504342018147/1000000000000 : ℝ) (504342018107/1000000000000 : ℝ) (126085504529/250000000000 : ℝ) (504342018123/1000000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 5 (504342018123/1000000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 6 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (119/1024 : ℝ))) 7 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (119/1024 : ℝ)) hmem 8 (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (119/1024 : ℝ))) hcmem 8 (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (119/1024 : ℝ)) (991750658477/1000000000000 : ℝ) (12396883231/12500000000 : ℝ) (252171009061/500000000000 : ℝ) (126085504533/250000000000 : ℝ) (1560172327/1953125000 : ℝ) (798808231443/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0021_exp_lower
  have heNumeric : (201923858993/100000000000 : ℝ)/4 ≤ Real.exp (-683573856443/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201923858993/100000000000 : ℝ)/4 ≤ Real.exp ((59/512 : ℝ)-(798808231443/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (59/512 : ℝ) (119/1024 : ℝ) (798808231443/1000000000000 : ℝ) (201923858993/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0022; no trusted numerical premise.
theorem cover7_leaf0022_exp_radius : (997909554103292051/1000000000000000000 : ℝ) ≤ Real.exp ((-15/896 : ℝ)/8) ∧ Real.exp ((-15/896 : ℝ)/8) ≤ (249477388525823013/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-15/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0022_exp_lower : (36723590938424913/40000000000000000 : ℝ) ≤ Real.exp ((-341840402809/500000000000 : ℝ)/8) ∧ Real.exp ((-341840402809/500000000000 : ℝ)/8) ≤ (459044886730311413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341840402809/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0022_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252377830697/125000000000 : ℝ) ≤ 4*Real.exp (119/1024 : ℝ)*Real.exp (-mu (radius 7 (15/128 : ℝ))) ∧ (2019/1000 : ℝ) < (252377830697/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (15/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0022_exp_radius
  have hrNumeric : (61462392599/62500000000 : ℝ) ≤ Real.exp (-15/896 : ℝ) ∧ Real.exp (-15/896 : ℝ) ≤ (196679656317/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61462392599/62500000000 : ℝ) ≤ (radius 7 (15/128 : ℝ)) ∧ (radius 7 (15/128 : ℝ)) ≤ (196679656317/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (15/128 : ℝ)) (61462392599/62500000000 : ℝ) (196679656317/200000000000 : ℝ) (181460242961/1000000000000 : ℝ) (181460242967/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (15/128 : ℝ)) (61462392599/62500000000 : ℝ) (196679656317/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (15/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61462392599/62500000000 : ℝ) (196679656317/200000000000 : ℝ) (123962392599/125000000000 : ℝ) (991699140793/1000000000000 : ℝ) (39666575987/40000000000 : ℝ) (991664399677/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (15/128 : ℝ)) 1 (123962392599/125000000000 : ℝ) (991699140793/1000000000000 : ℝ) (39666575987/40000000000 : ℝ) (991664399677/1000000000000 : ℝ) (991681770233/1000000000000 : ℝ) (198336354047/200000000000 : ℝ) (991681770081/1000000000000 : ℝ) (991681770083/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (15/128 : ℝ)) 2 (991681770233/1000000000000 : ℝ) (198336354047/200000000000 : ℝ) (991681770081/1000000000000 : ℝ) (991681770083/1000000000000 : ℝ) (991681770157/1000000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (15/128 : ℝ)) 3 (991681770157/1000000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (15/128 : ℝ)) 4 (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (15/128 : ℝ)) 5 (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (15/128 : ℝ)) 6 (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (15/128 : ℝ)) 7 (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (15/128 : ℝ))) (181460242961/1000000000000 : ℝ) (181460242967/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181460242961/1000000000000 : ℝ) (181460242967/1000000000000 : ℝ) (14768253037/25000000000 : ℝ) (147682530371/250000000000 : ℝ) (425981505421/1000000000000 : ℝ) (425981505429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 1 (14768253037/25000000000 : ℝ) (147682530371/250000000000 : ℝ) (425981505421/1000000000000 : ℝ) (425981505429/1000000000000 : ℝ) (10167116269/20000000000 : ℝ) (508355813457/1000000000000 : ℝ) (125409356321/250000000000 : ℝ) (501637425291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 2 (10167116269/20000000000 : ℝ) (508355813457/1000000000000 : ℝ) (125409356321/250000000000 : ℝ) (501637425291/1000000000000 : ℝ) (504996619367/1000000000000 : ℝ) (252498309687/500000000000 : ℝ) (126246361677/250000000000 : ℝ) (126246361679/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 3 (504996619367/1000000000000 : ℝ) (252498309687/500000000000 : ℝ) (126246361677/250000000000 : ℝ) (126246361679/250000000000 : ℝ) (504991033037/1000000000000 : ℝ) (100998206609/200000000000 : ℝ) (252495516503/500000000000 : ℝ) (100998206603/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 4 (504991033037/1000000000000 : ℝ) (100998206609/200000000000 : ℝ) (252495516503/500000000000 : ℝ) (100998206603/200000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 5 (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 6 (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (15/128 : ℝ))) 7 (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (15/128 : ℝ)) hmem 8 (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (15/128 : ℝ))) hcmem 8 (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (15/128 : ℝ)) (247920442539/250000000000 : ℝ) (991681770159/1000000000000 : ℝ) (504991033021/1000000000000 : ℝ) (50499103303/100000000000 : ℝ) (7998917431/10000000000 : ℝ) (399945871559/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0022_exp_lower
  have heNumeric : (252377830697/125000000000 : ℝ)/4 ≤ Real.exp (-341840402809/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252377830697/125000000000 : ℝ)/4 ≤ Real.exp ((119/1024 : ℝ)-(399945871559/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (119/1024 : ℝ) (15/128 : ℝ) (399945871559/500000000000 : ℝ) (252377830697/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0023; no trusted numerical premise.
theorem cover7_leaf0023_exp_radius : (997900853060431633/1000000000000000000 : ℝ) ≤ Real.exp ((-241/14336 : ℝ)/8) ∧ Real.exp ((-241/14336 : ℝ)/8) ≤ (498950426530215817/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-241/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0023_exp_lower : (91813993629501617/100000000000000000 : ℝ) ≤ Real.exp ((-683243711421/1000000000000 : ℝ)/8) ∧ Real.exp ((-683243711421/1000000000000 : ℝ)/8) ≤ (918139936295016171/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683243711421/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0023_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403981068311/200000000000 : ℝ) ≤ 4*Real.exp (15/128 : ℝ)*Real.exp (-mu (radius 7 (241/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403981068311/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (241/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0023_exp_radius
  have hrNumeric : (245832421889/250000000000 : ℝ) ≤ Real.exp (-241/14336 : ℝ) ∧ Real.exp (-241/14336 : ℝ) ≤ (983329687557/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245832421889/250000000000 : ℝ) ≤ (radius 7 (241/2048 : ℝ)) ∧ (radius 7 (241/2048 : ℝ)) ≤ (983329687557/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (241/2048 : ℝ)) (245832421889/250000000000 : ℝ) (983329687557/1000000000000 : ℝ) (181831585729/1000000000000 : ℝ) (22728948217/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (241/2048 : ℝ)) (245832421889/250000000000 : ℝ) (983329687557/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (241/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245832421889/250000000000 : ℝ) (983329687557/1000000000000 : ℝ) (495832421889/500000000000 : ℝ) (991664843779/1000000000000 : ℝ) (991629813769/1000000000000 : ℝ) (99162981377/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (241/2048 : ℝ)) 1 (495832421889/500000000000 : ℝ) (991664843779/1000000000000 : ℝ) (991629813769/1000000000000 : ℝ) (99162981377/100000000000 : ℝ) (991647328773/1000000000000 : ℝ) (39665893151/40000000000 : ℝ) (495823664309/500000000000 : ℝ) (49582366431/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (241/2048 : ℝ)) 2 (991647328773/1000000000000 : ℝ) (39665893151/40000000000 : ℝ) (495823664309/500000000000 : ℝ) (49582366431/50000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (241/2048 : ℝ)) 3 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (241/2048 : ℝ)) 4 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (241/2048 : ℝ)) 5 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (241/2048 : ℝ)) 6 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (241/2048 : ℝ)) 7 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (241/2048 : ℝ))) (181831585729/1000000000000 : ℝ) (22728948217/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181831585729/1000000000000 : ℝ) (22728948217/125000000000 : ℝ) (18466118527/31250000000 : ℝ) (147728948217/250000000000 : ℝ) (4264171499/10000000000 : ℝ) (426417149909/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 1 (18466118527/31250000000 : ℝ) (147728948217/250000000000 : ℝ) (4264171499/10000000000 : ℝ) (426417149909/1000000000000 : ℝ) (254333235691/500000000000 : ℝ) (508666471389/1000000000000 : ℝ) (250986368267/500000000000 : ℝ) (250986368271/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 2 (254333235691/500000000000 : ℝ) (508666471389/1000000000000 : ℝ) (250986368267/500000000000 : ℝ) (250986368271/500000000000 : ℝ) (252659801979/500000000000 : ℝ) (252659801983/500000000000 : ℝ) (101061704047/200000000000 : ℝ) (126327130061/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 3 (252659801979/500000000000 : ℝ) (252659801983/500000000000 : ℝ) (101061704047/200000000000 : ℝ) (126327130061/250000000000 : ℝ) (31582128881/62500000000 : ℝ) (101062812421/200000000000 : ℝ) (252657031033/500000000000 : ℝ) (20212562483/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 4 (31582128881/62500000000 : ℝ) (101062812421/200000000000 : ℝ) (252657031033/500000000000 : ℝ) (20212562483/40000000000 : ℝ) (505314062081/1000000000000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 5 (505314062081/1000000000000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 6 (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (241/2048 : ℝ))) 7 (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (241/2048 : ℝ)) hmem 8 (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (241/2048 : ℝ))) hcmem 8 (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (241/2048 : ℝ)) (198329465739/200000000000 : ℝ) (495823664349/500000000000 : ℝ) (394776611/781250000 : ℝ) (50531406209/100000000000 : ℝ) (800431211401/1000000000000 : ℝ) (800431211421/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0023_exp_lower
  have heNumeric : (403981068311/200000000000 : ℝ)/4 ≤ Real.exp (-683243711421/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403981068311/200000000000 : ℝ)/4 ≤ Real.exp ((15/128 : ℝ)-(800431211421/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (15/128 : ℝ) (241/2048 : ℝ) (800431211421/1000000000000 : ℝ) (403981068311/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0024; no trusted numerical premise.
theorem cover7_leaf0024_exp_radius : (498946076046718979/500000000000000000 : ℝ) ≤ Real.exp ((-121/7168 : ℝ)/8) ∧ Real.exp ((-121/7168 : ℝ)/8) ≤ (997892152093437959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-121/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0024_exp_lower : (183626847006124951/200000000000000000 : ℝ) ≤ Real.exp ((-10676459191/15625000000 : ℝ)/8) ∧ Real.exp ((-10676459191/15625000000 : ℝ)/8) ≤ (229533558757656189/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10676459191/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0024_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019805001607/1000000000000 : ℝ) ≤ 4*Real.exp (241/2048 : ℝ)*Real.exp (-mu (radius 7 (121/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019805001607/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (121/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0024_exp_radius
  have hrNumeric : (983261098313/1000000000000 : ℝ) ≤ Real.exp (-121/7168 : ℝ) ∧ Real.exp (-121/7168 : ℝ) ≤ (491630549157/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983261098313/1000000000000 : ℝ) ≤ (radius 7 (121/1024 : ℝ)) ∧ (radius 7 (121/1024 : ℝ)) ≤ (491630549157/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (121/1024 : ℝ)) (983261098313/1000000000000 : ℝ) (491630549157/500000000000 : ℝ) (182202120027/1000000000000 : ℝ) (182202120033/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (121/1024 : ℝ)) (983261098313/1000000000000 : ℝ) (491630549157/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (121/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983261098313/1000000000000 : ℝ) (491630549157/500000000000 : ℝ) (247907637289/250000000000 : ℝ) (991630549157/1000000000000 : ℝ) (991595229069/1000000000000 : ℝ) (99159522907/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (121/1024 : ℝ)) 1 (247907637289/250000000000 : ℝ) (991630549157/1000000000000 : ℝ) (991595229069/1000000000000 : ℝ) (99159522907/100000000000 : ℝ) (123951611139/125000000000 : ℝ) (495806444557/500000000000 : ℝ) (198322577791/200000000000 : ℝ) (991612888957/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (121/1024 : ℝ)) 2 (123951611139/125000000000 : ℝ) (495806444557/500000000000 : ℝ) (198322577791/200000000000 : ℝ) (991612888957/1000000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (121/1024 : ℝ)) 3 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (121/1024 : ℝ)) 4 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (121/1024 : ℝ)) 5 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (121/1024 : ℝ)) 6 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (121/1024 : ℝ)) 7 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (121/1024 : ℝ))) (182202120027/1000000000000 : ℝ) (182202120033/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182202120027/1000000000000 : ℝ) (182202120033/1000000000000 : ℝ) (591101060013/1000000000000 : ℝ) (591101060017/1000000000000 : ℝ) (213425701373/500000000000 : ℝ) (213425701377/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 1 (591101060013/1000000000000 : ℝ) (591101060017/1000000000000 : ℝ) (213425701373/500000000000 : ℝ) (213425701377/500000000000 : ℝ) (508976231379/1000000000000 : ℝ) (254488115693/500000000000 : ℝ) (502306994407/1000000000000 : ℝ) (100461398883/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 2 (508976231379/1000000000000 : ℝ) (254488115693/500000000000 : ℝ) (502306994407/1000000000000 : ℝ) (100461398883/200000000000 : ℝ) (505641612893/1000000000000 : ℝ) (505641612901/1000000000000 : ℝ) (252815308579/500000000000 : ℝ) (505630617167/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 3 (505641612893/1000000000000 : ℝ) (505641612901/1000000000000 : ℝ) (252815308579/500000000000 : ℝ) (505630617167/1000000000000 : ℝ) (20225444601/40000000000 : ℝ) (252818057517/500000000000 : ℝ) (101127222999/200000000000 : ℝ) (101127223001/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 4 (20225444601/40000000000 : ℝ) (252818057517/500000000000 : ℝ) (101127222999/200000000000 : ℝ) (101127223001/200000000000 : ℝ) (50563611501/100000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 5 (50563611501/100000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 6 (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (121/1024 : ℝ))) 7 (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (121/1024 : ℝ)) hmem 8 (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (121/1024 : ℝ))) hcmem 8 (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (121/1024 : ℝ)) (991612889033/1000000000000 : ℝ) (247903222259/250000000000 : ℝ) (505636115009/1000000000000 : ℝ) (25281805751/50000000000 : ℝ) (800969169453/1000000000000 : ℝ) (400484584737/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0024_exp_lower
  have heNumeric : (2019805001607/1000000000000 : ℝ)/4 ≤ Real.exp (-10676459191/15625000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019805001607/1000000000000 : ℝ)/4 ≤ Real.exp ((241/2048 : ℝ)-(400484584737/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (241/2048 : ℝ) (121/1024 : ℝ) (400484584737/500000000000 : ℝ) (2019805001607/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0000_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0000_certificate
#check SmaleRate.Proofs.cover7_leaf0001_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0001_certificate
#check SmaleRate.Proofs.cover7_leaf0002_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0002_certificate
#check SmaleRate.Proofs.cover7_leaf0003_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0003_certificate
#check SmaleRate.Proofs.cover7_leaf0004_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0004_certificate
#check SmaleRate.Proofs.cover7_leaf0005_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0005_certificate
#check SmaleRate.Proofs.cover7_leaf0006_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0006_certificate
#check SmaleRate.Proofs.cover7_leaf0007_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0007_certificate
#check SmaleRate.Proofs.cover7_leaf0008_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0008_certificate
#check SmaleRate.Proofs.cover7_leaf0009_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0009_certificate
#check SmaleRate.Proofs.cover7_leaf0010_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0010_certificate
#check SmaleRate.Proofs.cover7_leaf0011_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0011_certificate
#check SmaleRate.Proofs.cover7_leaf0012_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0012_certificate
#check SmaleRate.Proofs.cover7_leaf0013_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0013_certificate
#check SmaleRate.Proofs.cover7_leaf0014_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0014_certificate
#check SmaleRate.Proofs.cover7_leaf0015_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0015_certificate
#check SmaleRate.Proofs.cover7_leaf0016_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0016_certificate
#check SmaleRate.Proofs.cover7_leaf0017_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0017_certificate
#check SmaleRate.Proofs.cover7_leaf0018_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0018_certificate
#check SmaleRate.Proofs.cover7_leaf0019_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0019_certificate
#check SmaleRate.Proofs.cover7_leaf0020_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0020_certificate
#check SmaleRate.Proofs.cover7_leaf0021_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0021_certificate
#check SmaleRate.Proofs.cover7_leaf0022_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0022_certificate
#check SmaleRate.Proofs.cover7_leaf0023_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0023_certificate
#check SmaleRate.Proofs.cover7_leaf0024_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0024_certificate
