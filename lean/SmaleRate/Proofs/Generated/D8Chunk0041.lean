/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1025; no trusted numerical premise.
theorem cover8_leaf1025_exp_radius : (31187572556028689/31250000000000000 : ℝ) ≤ Real.exp ((-33549/2097152 : ℝ)/8) ∧ Real.exp ((-33549/2097152 : ℝ)/8) ≤ (998002321792918049/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33549/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1025_exp_lower : (230028369462891631/250000000000000000 : ℝ) ≤ Real.exp ((-85256469559959/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256469559959/128000000000000 : ℝ)/8) ≤ (36804539114062661/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256469559959/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1025_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451035381/500000000000 : ℝ) ≤ 4*Real.exp (67097/524288 : ℝ)*Real.exp (-mu (radius 8 (33549/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451035381/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33549/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1025_exp_radius
  have hrNumeric : (246032467281/250000000000 : ℝ) ≤ Real.exp (-33549/2097152 : ℝ) ∧ Real.exp (-33549/2097152 : ℝ) ≤ (7873038953/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246032467281/250000000000 : ℝ) ≤ (radius 8 (33549/262144 : ℝ)) ∧ (radius 8 (33549/262144 : ℝ)) ≤ (7873038953/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33549/262144 : ℝ)) (246032467281/250000000000 : ℝ) (7873038953/8000000000 : ℝ) (177449713147/1000000000000 : ℝ) (177449713153/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33549/262144 : ℝ)) (246032467281/250000000000 : ℝ) (7873038953/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246032467281/250000000000 : ℝ) (7873038953/8000000000 : ℝ) (496032467281/500000000000 : ℝ) (992064934563/1000000000000 : ℝ) (992033199607/1000000000000 : ℝ) (992033199609/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 1 (496032467281/500000000000 : ℝ) (992064934563/1000000000000 : ℝ) (992033199607/1000000000000 : ℝ) (992033199609/1000000000000 : ℝ) (248012266771/250000000000 : ℝ) (496024533543/500000000000 : ℝ) (992049066957/1000000000000 : ℝ) (12400613337/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 2 (248012266771/250000000000 : ℝ) (496024533543/500000000000 : ℝ) (992049066957/1000000000000 : ℝ) (12400613337/12500000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 3 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 4 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 5 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 6 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33549/262144 : ℝ)) 7 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33549/262144 : ℝ))) (177449713147/1000000000000 : ℝ) (177449713153/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177449713147/1000000000000 : ℝ) (177449713153/1000000000000 : ℝ) (588724856573/1000000000000 : ℝ) (588724856577/1000000000000 : ℝ) (105311951229/250000000000 : ℝ) (105311951231/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 1 (588724856573/1000000000000 : ℝ) (588724856577/1000000000000 : ℝ) (105311951229/250000000000 : ℝ) (105311951231/250000000000 : ℝ) (63123291343/125000000000 : ℝ) (504986330751/1000000000000 : ℝ) (12449875841/25000000000 : ℝ) (31124689603/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 2 (63123291343/125000000000 : ℝ) (504986330751/1000000000000 : ℝ) (12449875841/25000000000 : ℝ) (31124689603/62500000000 : ℝ) (31343167637/62500000000 : ℝ) (2507453411/5000000000 : ℝ) (501478498807/1000000000000 : ℝ) (979450193/1953125000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 3 (31343167637/62500000000 : ℝ) (2507453411/5000000000 : ℝ) (501478498807/1000000000000 : ℝ) (979450193/1953125000 : ℝ) (501484590499/1000000000000 : ℝ) (125371147627/250000000000 : ℝ) (250742295231/500000000000 : ℝ) (62685573809/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 4 (501484590499/1000000000000 : ℝ) (125371147627/250000000000 : ℝ) (250742295231/500000000000 : ℝ) (62685573809/125000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 5 (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 6 (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33549/262144 : ℝ))) 7 (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33549/262144 : ℝ)) hmem 8 (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33549/262144 : ℝ))) hcmem 8 (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33549/262144 : ℝ)) (49602453351/50000000000 : ℝ) (992049067023/1000000000000 : ℝ) (6268557381/12500000000 : ℝ) (50148459049/100000000000 : ℝ) (397021769817/500000000000 : ℝ) (794043539653/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1025_exp_lower
  have heNumeric : (1027451035381/500000000000 : ℝ)/4 ≤ Real.exp (-85256469559959/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451035381/500000000000 : ℝ)/4 ≤ Real.exp ((67097/524288 : ℝ)-(794043539653/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67097/524288 : ℝ) (33549/262144 : ℝ) (794043539653/1000000000000 : ℝ) (1027451035381/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1026; no trusted numerical premise.
theorem cover8_leaf1026_exp_radius : (499001146025065777/500000000000000000 : ℝ) ≤ Real.exp ((-67099/4194304 : ℝ)/8) ∧ Real.exp ((-67099/4194304 : ℝ)/8) ≤ (199600458410026311/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67099/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1026_exp_lower : (230028369554892421/250000000000000000 : ℝ) ≤ Real.exp ((-42628234575203/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628234575203/64000000000000 : ℝ)/8) ≤ (184022695643913937/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628234575203/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1026_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902077337/1000000000000 : ℝ) ≤ 4*Real.exp (33549/262144 : ℝ)*Real.exp (-mu (radius 8 (67099/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902077337/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67099/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1026_exp_radius
  have hrNumeric : (98412963449/100000000000 : ℝ) ≤ Real.exp (-67099/4194304 : ℝ) ∧ Real.exp (-67099/4194304 : ℝ) ≤ (984129634491/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98412963449/100000000000 : ℝ) ≤ (radius 8 (67099/524288 : ℝ)) ∧ (radius 8 (67099/524288 : ℝ)) ≤ (984129634491/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67099/524288 : ℝ)) (98412963449/100000000000 : ℝ) (984129634491/1000000000000 : ℝ) (88725507207/500000000000 : ℝ) (8872550721/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67099/524288 : ℝ)) (98412963449/100000000000 : ℝ) (984129634491/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98412963449/100000000000 : ℝ) (984129634491/1000000000000 : ℝ) (198412963449/200000000000 : ℝ) (496032408623/500000000000 : ℝ) (248008270337/250000000000 : ℝ) (19840661627/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 1 (198412963449/200000000000 : ℝ) (496032408623/500000000000 : ℝ) (248008270337/250000000000 : ℝ) (19840661627/20000000000 : ℝ) (62003059331/62500000000 : ℝ) (496024474649/500000000000 : ℝ) (992048949169/1000000000000 : ℝ) (248012237293/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 2 (62003059331/62500000000 : ℝ) (496024474649/500000000000 : ℝ) (992048949169/1000000000000 : ℝ) (248012237293/250000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 3 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 4 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 5 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 6 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67099/524288 : ℝ)) 7 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67099/524288 : ℝ))) (88725507207/500000000000 : ℝ) (8872550721/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88725507207/500000000000 : ℝ) (8872550721/50000000000 : ℝ) (588725507207/1000000000000 : ℝ) (58872550721/100000000000 : ℝ) (105312337363/250000000000 : ℝ) (21062467473/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 1 (588725507207/1000000000000 : ℝ) (58872550721/100000000000 : ℝ) (105312337363/250000000000 : ℝ) (21062467473/50000000000 : ℝ) (504987428329/1000000000000 : ℝ) (100997485667/200000000000 : ℝ) (497996221789/1000000000000 : ℝ) (124499055449/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 2 (504987428329/1000000000000 : ℝ) (100997485667/200000000000 : ℝ) (497996221789/1000000000000 : ℝ) (124499055449/250000000000 : ℝ) (501491825059/1000000000000 : ℝ) (250745912533/500000000000 : ℝ) (250739821009/500000000000 : ℝ) (20059185681/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 3 (501491825059/1000000000000 : ℝ) (250745912533/500000000000 : ℝ) (250739821009/500000000000 : ℝ) (20059185681/40000000000 : ℝ) (250742866769/500000000000 : ℝ) (250742866773/500000000000 : ℝ) (501485733501/1000000000000 : ℝ) (501485733509/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 4 (250742866769/500000000000 : ℝ) (250742866773/500000000000 : ℝ) (501485733501/1000000000000 : ℝ) (501485733509/1000000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 5 (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 6 (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67099/524288 : ℝ))) 7 (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67099/524288 : ℝ)) hmem 8 (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67099/524288 : ℝ))) hcmem 8 (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67099/524288 : ℝ)) (62003059327/62500000000 : ℝ) (198409789847/200000000000 : ℝ) (501485733519/1000000000000 : ℝ) (62685716691/125000000000 : ℝ) (99255680473/125000000000 : ℝ) (397022721901/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1026_exp_lower
  have heNumeric : (2054902077337/1000000000000 : ℝ)/4 ≤ Real.exp (-42628234575203/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902077337/1000000000000 : ℝ)/4 ≤ Real.exp ((33549/262144 : ℝ)-(397022721901/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33549/262144 : ℝ) (67099/524288 : ℝ) (397022721901/500000000000 : ℝ) (2054902077337/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1027; no trusted numerical premise.
theorem cover8_leaf1027_exp_radius : (499001131153672973/500000000000000000 : ℝ) ≤ Real.exp ((-16775/1048576 : ℝ)/8) ∧ Real.exp ((-16775/1048576 : ℝ)/8) ≤ (998002262307345947/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16775/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1027_exp_lower : (920113478588492957/1000000000000000000 : ℝ) ≤ Real.exp ((-85256468739829/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256468739829/128000000000000 : ℝ)/8) ≤ (460056739294246479/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256468739829/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1027_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902083929/1000000000000 : ℝ) ≤ 4*Real.exp (67099/524288 : ℝ)*Real.exp (-mu (radius 8 (16775/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902083929/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16775/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1027_exp_radius
  have hrNumeric : (196825879971/200000000000 : ℝ) ≤ Real.exp (-16775/1048576 : ℝ) ∧ Real.exp (-16775/1048576 : ℝ) ≤ (61508087491/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196825879971/200000000000 : ℝ) ≤ (radius 8 (16775/131072 : ℝ)) ∧ (radius 8 (16775/131072 : ℝ)) ≤ (61508087491/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16775/131072 : ℝ)) (196825879971/200000000000 : ℝ) (61508087491/62500000000 : ℝ) (44363078919/250000000000 : ℝ) (177452315683/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16775/131072 : ℝ)) (196825879971/200000000000 : ℝ) (61508087491/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196825879971/200000000000 : ℝ) (61508087491/62500000000 : ℝ) (992064699927/1000000000000 : ℝ) (124008087491/125000000000 : ℝ) (62002060193/62500000000 : ℝ) (99203296309/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 1 (992064699927/1000000000000 : ℝ) (124008087491/125000000000 : ℝ) (62002060193/62500000000 : ℝ) (99203296309/100000000000 : ℝ) (992048831507/1000000000000 : ℝ) (992048831509/1000000000000 : ℝ) (49602441569/50000000000 : ℝ) (992048831383/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 2 (992048831507/1000000000000 : ℝ) (992048831509/1000000000000 : ℝ) (49602441569/50000000000 : ℝ) (992048831383/1000000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 3 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 4 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 5 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 6 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16775/131072 : ℝ)) 7 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16775/131072 : ℝ))) (44363078919/250000000000 : ℝ) (177452315683/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44363078919/250000000000 : ℝ) (177452315683/1000000000000 : ℝ) (294363078919/500000000000 : ℝ) (294363078921/500000000000 : ℝ) (52656361747/125000000000 : ℝ) (84250178797/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 1 (294363078919/500000000000 : ℝ) (294363078921/500000000000 : ℝ) (52656361747/125000000000 : ℝ) (84250178797/200000000000 : ℝ) (504988525907/1000000000000 : ℝ) (252494262957/500000000000 : ℝ) (497997409929/1000000000000 : ℝ) (497997409937/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 2 (504988525907/1000000000000 : ℝ) (252494262957/500000000000 : ℝ) (497997409929/1000000000000 : ℝ) (497997409937/1000000000000 : ℝ) (250746483959/500000000000 : ℝ) (250746483963/500000000000 : ℝ) (25074039261/50000000000 : ℝ) (501480785229/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 3 (250746483959/500000000000 : ℝ) (250746483963/500000000000 : ℝ) (25074039261/50000000000 : ℝ) (501480785229/1000000000000 : ℝ) (501486876569/1000000000000 : ℝ) (250743438289/500000000000 : ℝ) (125371719133/250000000000 : ℝ) (501486876541/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 4 (501486876569/1000000000000 : ℝ) (250743438289/500000000000 : ℝ) (125371719133/250000000000 : ℝ) (501486876541/1000000000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 5 (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 6 (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16775/131072 : ℝ))) 7 (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16775/131072 : ℝ)) hmem 8 (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16775/131072 : ℝ))) hcmem 8 (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16775/131072 : ℝ)) (992048831443/1000000000000 : ℝ) (496024415723/500000000000 : ℝ) (10029737531/20000000000 : ℝ) (6268585957/12500000000 : ℝ) (794047347923/1000000000000 : ℝ) (794047347943/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1027_exp_lower
  have heNumeric : (2054902083929/1000000000000 : ℝ)/4 ≤ Real.exp (-85256468739829/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902083929/1000000000000 : ℝ)/4 ≤ Real.exp ((67099/524288 : ℝ)-(794047347943/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67099/524288 : ℝ) (16775/131072 : ℝ) (794047347943/1000000000000 : ℝ) (2054902083929/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1028; no trusted numerical premise.
theorem cover8_leaf1028_exp_radius : (124750279070570153/125000000000000000 : ℝ) ≤ Real.exp ((-67101/4194304 : ℝ)/8) ∧ Real.exp ((-67101/4194304 : ℝ)/8) ≤ (39920089302582449/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67101/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1028_exp_lower : (92011347896017657/100000000000000000 : ℝ) ≤ Real.exp ((-4262823416309/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262823416309/6400000000000 : ℝ)/8) ≤ (920113478960176571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262823416309/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1028_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902090569/1000000000000 : ℝ) ≤ 4*Real.exp (16775/131072 : ℝ)*Real.exp (-mu (radius 8 (67101/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902090569/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67101/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1028_exp_radius
  have hrNumeric : (49206458261/50000000000 : ℝ) ≤ Real.exp (-67101/4194304 : ℝ) ∧ Real.exp (-67101/4194304 : ℝ) ≤ (984129165221/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49206458261/50000000000 : ℝ) ≤ (radius 8 (67101/524288 : ℝ)) ∧ (radius 8 (67101/524288 : ℝ)) ≤ (984129165221/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67101/524288 : ℝ)) (49206458261/50000000000 : ℝ) (984129165221/1000000000000 : ℝ) (177453616929/1000000000000 : ℝ) (22181702117/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67101/524288 : ℝ)) (49206458261/50000000000 : ℝ) (984129165221/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49206458261/50000000000 : ℝ) (984129165221/1000000000000 : ℝ) (99206458261/100000000000 : ℝ) (992064582611/1000000000000 : ℝ) (992032844829/1000000000000 : ℝ) (99203284483/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 1 (99206458261/100000000000 : ℝ) (992064582611/1000000000000 : ℝ) (992032844829/1000000000000 : ℝ) (99203284483/100000000000 : ℝ) (992048713719/1000000000000 : ℝ) (992048713721/1000000000000 : ℝ) (124006089199/125000000000 : ℝ) (496024356797/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 2 (992048713719/1000000000000 : ℝ) (992048713721/1000000000000 : ℝ) (124006089199/125000000000 : ℝ) (496024356797/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 3 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 4 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 5 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 6 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67101/524288 : ℝ)) 7 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67101/524288 : ℝ))) (177453616929/1000000000000 : ℝ) (22181702117/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177453616929/1000000000000 : ℝ) (22181702117/125000000000 : ℝ) (36795425529/62500000000 : ℝ) (147181702117/250000000000 : ℝ) (105313109621/250000000000 : ℝ) (421252438493/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 1 (36795425529/62500000000 : ℝ) (147181702117/250000000000 : ℝ) (105313109621/250000000000 : ℝ) (421252438493/1000000000000 : ℝ) (252494811737/500000000000 : ℝ) (504989623481/1000000000000 : ℝ) (62249824757/125000000000 : ℝ) (31124912379/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 2 (252494811737/500000000000 : ℝ) (504989623481/1000000000000 : ℝ) (62249824757/125000000000 : ℝ) (31124912379/62500000000 : ℝ) (100298822153/200000000000 : ℝ) (501494110773/1000000000000 : ℝ) (501481928411/1000000000000 : ℝ) (501481928419/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 3 (100298822153/200000000000 : ℝ) (501494110773/1000000000000 : ℝ) (501481928411/1000000000000 : ℝ) (501481928419/1000000000000 : ℝ) (125372004897/250000000000 : ℝ) (125372004899/250000000000 : ℝ) (501488019551/1000000000000 : ℝ) (12537200489/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 4 (125372004897/250000000000 : ℝ) (125372004899/250000000000 : ℝ) (501488019551/1000000000000 : ℝ) (12537200489/25000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 5 (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 6 (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67101/524288 : ℝ))) 7 (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67101/524288 : ℝ)) hmem 8 (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67101/524288 : ℝ))) hcmem 8 (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67101/524288 : ℝ)) (198409742731/200000000000 : ℝ) (496024356829/500000000000 : ℝ) (501488019569/1000000000000 : ℝ) (250744009789/500000000000 : ℝ) (794049252043/1000000000000 : ℝ) (39702462603/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1028_exp_lower
  have heNumeric : (2054902090569/1000000000000 : ℝ)/4 ≤ Real.exp (-4262823416309/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902090569/1000000000000 : ℝ)/4 ≤ Real.exp ((16775/131072 : ℝ)-(39702462603/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16775/131072 : ℝ) (67101/524288 : ℝ) (39702462603/50000000000 : ℝ) (2054902090569/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1029; no trusted numerical premise.
theorem cover8_leaf1029_exp_radius : (998002202821777389/1000000000000000000 : ℝ) ≤ Real.exp ((-33551/2097152 : ℝ)/8) ∧ Real.exp ((-33551/2097152 : ℝ)/8) ≤ (99800220282177739/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33551/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1029_exp_lower : (36804539173384821/40000000000000000 : ℝ) ≤ Real.exp ((-85256467909459/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256467909459/128000000000000 : ℝ)/8) ≤ (460056739667310263/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256467909459/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1029_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902097259/1000000000000 : ℝ) ≤ 4*Real.exp (67101/524288 : ℝ)*Real.exp (-mu (radius 8 (33551/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902097259/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33551/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1029_exp_radius
  have hrNumeric : (492064465293/500000000000 : ℝ) ≤ Real.exp (-33551/2097152 : ℝ) ∧ Real.exp (-33551/2097152 : ℝ) ≤ (984128930587/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492064465293/500000000000 : ℝ) ≤ (radius 8 (33551/262144 : ℝ)) ∧ (radius 8 (33551/262144 : ℝ)) ≤ (984128930587/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33551/262144 : ℝ)) (492064465293/500000000000 : ℝ) (984128930587/1000000000000 : ℝ) (177454918167/1000000000000 : ℝ) (177454918173/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33551/262144 : ℝ)) (492064465293/500000000000 : ℝ) (984128930587/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492064465293/500000000000 : ℝ) (984128930587/1000000000000 : ℝ) (992064465293/1000000000000 : ℝ) (496032232647/500000000000 : ℝ) (99203272657/100000000000 : ℝ) (992032726571/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 1 (992064465293/1000000000000 : ℝ) (496032232647/500000000000 : ℝ) (99203272657/100000000000 : ℝ) (992032726571/1000000000000 : ℝ) (992048595931/1000000000000 : ℝ) (992048595933/1000000000000 : ℝ) (248012148951/250000000000 : ℝ) (496024297903/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 2 (992048595931/1000000000000 : ℝ) (992048595933/1000000000000 : ℝ) (248012148951/250000000000 : ℝ) (496024297903/500000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 3 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 4 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 5 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 6 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33551/262144 : ℝ)) 7 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33551/262144 : ℝ))) (177454918167/1000000000000 : ℝ) (177454918173/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177454918167/1000000000000 : ℝ) (177454918173/1000000000000 : ℝ) (588727459083/1000000000000 : ℝ) (588727459087/1000000000000 : ℝ) (52656747871/125000000000 : ℝ) (1645523371/3906250000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 1 (588727459083/1000000000000 : ℝ) (588727459087/1000000000000 : ℝ) (52656747871/125000000000 : ℝ) (1645523371/3906250000 : ℝ) (20199628841/40000000000 : ℝ) (63123840129/125000000000 : ℝ) (99599957233/200000000000 : ℝ) (497999786173/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 2 (20199628841/40000000000 : ℝ) (63123840129/125000000000 : ℝ) (99599957233/200000000000 : ℝ) (497999786173/1000000000000 : ℝ) (100299050719/200000000000 : ℝ) (501495253603/1000000000000 : ℝ) (15671345987/31250000000 : ℝ) (62685383949/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 3 (100299050719/200000000000 : ℝ) (501495253603/1000000000000 : ℝ) (15671345987/31250000000 : ℝ) (62685383949/125000000000 : ℝ) (501489162589/1000000000000 : ℝ) (250744581299/500000000000 : ℝ) (62686145319/125000000000 : ℝ) (501489162561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 4 (501489162589/1000000000000 : ℝ) (250744581299/500000000000 : ℝ) (62686145319/125000000000 : ℝ) (501489162561/1000000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 5 (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 6 (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33551/262144 : ℝ))) 7 (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33551/262144 : ℝ)) hmem 8 (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33551/262144 : ℝ))) hcmem 8 (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33551/262144 : ℝ)) (992048595867/1000000000000 : ℝ) (99204859587/100000000000 : ℝ) (50148916257/100000000000 : ℝ) (25074458129/50000000000 : ℝ) (397025578067/500000000000 : ℝ) (794051156153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1029_exp_lower
  have heNumeric : (2054902097259/1000000000000 : ℝ)/4 ≤ Real.exp (-85256467909459/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902097259/1000000000000 : ℝ)/4 ≤ Real.exp ((67101/524288 : ℝ)-(794051156153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67101/524288 : ℝ) (33551/262144 : ℝ) (794051156153/1000000000000 : ℝ) (2054902097259/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1030; no trusted numerical premise.
theorem cover8_leaf1030_exp_radius : (24950054326974861/25000000000000000 : ℝ) ≤ Real.exp ((-67103/4194304 : ℝ)/8) ∧ Real.exp ((-67103/4194304 : ℝ)/8) ≤ (998002173078994441/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67103/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1030_exp_lower : (184022695942065927/200000000000000000 : ℝ) ≤ Real.exp ((-8525646749133/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525646749133/12800000000000 : ℝ)/8) ≤ (230028369927582409/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525646749133/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1030_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725525993/250000000000 : ℝ) ≤ 4*Real.exp (33551/262144 : ℝ)*Real.exp (-mu (radius 8 (67103/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725525993/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67103/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1030_exp_radius
  have hrNumeric : (984128695951/1000000000000 : ℝ) ≤ Real.exp (-67103/4194304 : ℝ) ∧ Real.exp (-67103/4194304 : ℝ) ≤ (61508043497/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984128695951/1000000000000 : ℝ) ≤ (radius 8 (67103/524288 : ℝ)) ∧ (radius 8 (67103/524288 : ℝ)) ≤ (61508043497/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67103/524288 : ℝ)) (984128695951/1000000000000 : ℝ) (61508043497/62500000000 : ℝ) (887281097/5000000000 : ℝ) (88728109703/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67103/524288 : ℝ)) (984128695951/1000000000000 : ℝ) (61508043497/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984128695951/1000000000000 : ℝ) (61508043497/62500000000 : ℝ) (39682573919/40000000000 : ℝ) (124008043497/125000000000 : ℝ) (99203260831/100000000000 : ℝ) (992032608311/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 1 (39682573919/40000000000 : ℝ) (124008043497/125000000000 : ℝ) (99203260831/100000000000 : ℝ) (992032608311/1000000000000 : ℝ) (496024239071/500000000000 : ℝ) (15500757471/15625000000 : ℝ) (198409695603/200000000000 : ℝ) (992048478017/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 2 (496024239071/500000000000 : ℝ) (15500757471/15625000000 : ℝ) (198409695603/200000000000 : ℝ) (992048478017/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 3 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 4 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 5 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 6 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67103/524288 : ℝ)) 7 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67103/524288 : ℝ))) (887281097/5000000000 : ℝ) (88728109703/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (887281097/5000000000 : ℝ) (88728109703/500000000000 : ℝ) (5887281097/10000000000 : ℝ) (588728109703/1000000000000 : ℝ) (421255527441/1000000000000 : ℝ) (421255527449/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 1 (5887281097/10000000000 : ℝ) (588728109703/1000000000000 : ℝ) (421255527441/1000000000000 : ℝ) (421255527449/1000000000000 : ℝ) (50499181857/100000000000 : ℝ) (31561988661/62500000000 : ℝ) (498000974267/1000000000000 : ℝ) (249000487137/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 2 (50499181857/100000000000 : ℝ) (31561988661/62500000000 : ℝ) (498000974267/1000000000000 : ℝ) (249000487137/500000000000 : ℝ) (250748198209/500000000000 : ℝ) (20059855857/40000000000 : ℝ) (501484214751/1000000000000 : ℝ) (250742107379/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 3 (250748198209/500000000000 : ℝ) (20059855857/40000000000 : ℝ) (501484214751/1000000000000 : ℝ) (250742107379/500000000000 : ℝ) (31343144099/62500000000 : ℝ) (62686288199/125000000000 : ℝ) (501490305547/1000000000000 : ℝ) (100298061111/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 4 (31343144099/62500000000 : ℝ) (62686288199/125000000000 : ℝ) (501490305547/1000000000000 : ℝ) (100298061111/200000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 5 (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 6 (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67103/524288 : ℝ))) 7 (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67103/524288 : ℝ)) hmem 8 (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67103/524288 : ℝ))) hcmem 8 (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67103/524288 : ℝ)) (496024239039/500000000000 : ℝ) (992048478081/1000000000000 : ℝ) (100298061113/200000000000 : ℝ) (250745152787/500000000000 : ℝ) (794053060217/1000000000000 : ℝ) (158810612047/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1030_exp_lower
  have heNumeric : (513725525993/250000000000 : ℝ)/4 ≤ Real.exp (-8525646749133/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725525993/250000000000 : ℝ)/4 ≤ Real.exp ((33551/262144 : ℝ)-(158810612047/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33551/262144 : ℝ) (67103/524288 : ℝ) (158810612047/200000000000 : ℝ) (513725525993/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1031; no trusted numerical premise.
theorem cover8_leaf1031_exp_radius : (998002143336212377/1000000000000000000 : ℝ) ≤ Real.exp ((-2097/131072 : ℝ)/8) ∧ Real.exp ((-2097/131072 : ℝ)/8) ≤ (499001071668106189/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2097/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1031_exp_lower : (920113480088109001/1000000000000000000 : ℝ) ≤ Real.exp ((-85256467070897/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256467070897/128000000000000 : ℝ)/8) ≤ (460056740044054501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256467070897/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1031_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451055361/500000000000 : ℝ) ≤ 4*Real.exp (67103/524288 : ℝ)*Real.exp (-mu (radius 8 (2097/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451055361/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2097/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1031_exp_radius
  have hrNumeric : (246032115329/250000000000 : ℝ) ≤ Real.exp (-2097/131072 : ℝ) ∧ Real.exp (-2097/131072 : ℝ) ≤ (984128461317/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246032115329/250000000000 : ℝ) ≤ (radius 8 (2097/16384 : ℝ)) ∧ (radius 8 (2097/16384 : ℝ)) ≤ (984128461317/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2097/16384 : ℝ)) (246032115329/250000000000 : ℝ) (984128461317/1000000000000 : ℝ) (177457520623/1000000000000 : ℝ) (17745752063/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2097/16384 : ℝ)) (246032115329/250000000000 : ℝ) (984128461317/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246032115329/250000000000 : ℝ) (984128461317/1000000000000 : ℝ) (496032115329/500000000000 : ℝ) (992064230659/1000000000000 : ℝ) (19840649801/20000000000 : ℝ) (248008122513/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 1 (496032115329/500000000000 : ℝ) (992064230659/1000000000000 : ℝ) (19840649801/20000000000 : ℝ) (248008122513/250000000000 : ℝ) (496024180177/500000000000 : ℝ) (248012090089/250000000000 : ℝ) (992048360227/1000000000000 : ℝ) (992048360229/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 2 (496024180177/500000000000 : ℝ) (248012090089/250000000000 : ℝ) (992048360227/1000000000000 : ℝ) (992048360229/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 3 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 4 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 5 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 6 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2097/16384 : ℝ)) 7 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2097/16384 : ℝ))) (177457520623/1000000000000 : ℝ) (17745752063/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177457520623/1000000000000 : ℝ) (17745752063/100000000000 : ℝ) (588728760311/1000000000000 : ℝ) (117745752063/200000000000 : ℝ) (52657133987/125000000000 : ℝ) (210628535953/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 1 (588728760311/1000000000000 : ℝ) (117745752063/200000000000 : ℝ) (52657133987/125000000000 : ℝ) (210628535953/500000000000 : ℝ) (504992916103/1000000000000 : ℝ) (504992916111/1000000000000 : ℝ) (249001081177/500000000000 : ℝ) (249001081181/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 2 (504992916103/1000000000000 : ℝ) (504992916111/1000000000000 : ℝ) (249001081177/500000000000 : ℝ) (249001081181/500000000000 : ℝ) (125374384807/250000000000 : ℝ) (501497539237/1000000000000 : ℝ) (31342834869/62500000000 : ℝ) (501485357913/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 3 (125374384807/250000000000 : ℝ) (501497539237/1000000000000 : ℝ) (31342834869/62500000000 : ℝ) (501485357913/1000000000000 : ℝ) (250745724283/500000000000 : ℝ) (20059657943/40000000000 : ℝ) (501491448529/1000000000000 : ℝ) (501491448539/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 4 (250745724283/500000000000 : ℝ) (20059657943/40000000000 : ℝ) (501491448529/1000000000000 : ℝ) (501491448539/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 5 (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 6 (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2097/16384 : ℝ))) 7 (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2097/16384 : ℝ)) hmem 8 (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2097/16384 : ℝ))) hcmem 8 (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2097/16384 : ℝ)) (99204836029/100000000000 : ℝ) (992048360293/1000000000000 : ℝ) (501491448547/1000000000000 : ℝ) (501491448557/1000000000000 : ℝ) (19851374107/25000000000 : ℝ) (794054964299/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1031_exp_lower
  have heNumeric : (1027451055361/500000000000 : ℝ)/4 ≤ Real.exp (-85256467070897/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451055361/500000000000 : ℝ)/4 ≤ Real.exp ((67103/524288 : ℝ)-(794054964299/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67103/524288 : ℝ) (2097/16384 : ℝ) (794054964299/1000000000000 : ℝ) (1027451055361/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1032; no trusted numerical premise.
theorem cover8_leaf1032_exp_radius : (998002113593431201/1000000000000000000 : ℝ) ≤ Real.exp ((-67105/4194304 : ℝ)/8) ∧ Real.exp ((-67105/4194304 : ℝ)/8) ≤ (499001056796715601/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67105/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1032_exp_lower : (230028370117277191/250000000000000000 : ℝ) ≤ Real.exp ((-532852916543/800000000000 : ℝ)/8) ∧ Real.exp ((-532852916543/800000000000 : ℝ)/8) ≤ (184022696093821753/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532852916543/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1032_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902117529/1000000000000 : ℝ) ≤ 4*Real.exp (2097/16384 : ℝ)*Real.exp (-mu (radius 8 (67105/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902117529/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67105/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1032_exp_radius
  have hrNumeric : (492064113341/500000000000 : ℝ) ≤ Real.exp (-67105/4194304 : ℝ) ∧ Real.exp (-67105/4194304 : ℝ) ≤ (984128226683/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492064113341/500000000000 : ℝ) ≤ (radius 8 (67105/524288 : ℝ)) ∧ (radius 8 (67105/524288 : ℝ)) ≤ (984128226683/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67105/524288 : ℝ)) (492064113341/500000000000 : ℝ) (984128226683/1000000000000 : ℝ) (177458821831/1000000000000 : ℝ) (177458821837/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67105/524288 : ℝ)) (492064113341/500000000000 : ℝ) (984128226683/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492064113341/500000000000 : ℝ) (984128226683/1000000000000 : ℝ) (992064113341/1000000000000 : ℝ) (496032056671/500000000000 : ℝ) (992032371791/1000000000000 : ℝ) (62002023237/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 1 (992064113341/1000000000000 : ℝ) (496032056671/500000000000 : ℝ) (992032371791/1000000000000 : ℝ) (62002023237/62500000000 : ℝ) (496024121283/500000000000 : ℝ) (992048242567/1000000000000 : ℝ) (992048242439/1000000000000 : ℝ) (992048242441/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 2 (496024121283/500000000000 : ℝ) (992048242567/1000000000000 : ℝ) (992048242439/1000000000000 : ℝ) (992048242441/1000000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 3 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 4 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 5 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 6 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67105/524288 : ℝ)) 7 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67105/524288 : ℝ))) (177458821831/1000000000000 : ℝ) (177458821837/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177458821831/1000000000000 : ℝ) (177458821837/1000000000000 : ℝ) (117745882183/200000000000 : ℝ) (588729410919/1000000000000 : ℝ) (52657327041/125000000000 : ℝ) (26328663521/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 1 (117745882183/200000000000 : ℝ) (588729410919/1000000000000 : ℝ) (52657327041/125000000000 : ℝ) (26328663521/62500000000 : ℝ) (504994013621/1000000000000 : ℝ) (126248503407/250000000000 : ℝ) (62250418803/125000000000 : ℝ) (498003350431/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 2 (504994013621/1000000000000 : ℝ) (126248503407/250000000000 : ℝ) (62250418803/125000000000 : ℝ) (498003350431/1000000000000 : ℝ) (250749341011/500000000000 : ℝ) (50149868203/100000000000 : ℝ) (501486501041/1000000000000 : ℝ) (501486501049/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 3 (250749341011/500000000000 : ℝ) (50149868203/100000000000 : ℝ) (501486501041/1000000000000 : ℝ) (501486501049/1000000000000 : ℝ) (501492591531/1000000000000 : ℝ) (25074629577/50000000000 : ℝ) (250746295747/500000000000 : ℝ) (501492591503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 4 (501492591531/1000000000000 : ℝ) (25074629577/50000000000 : ℝ) (250746295747/500000000000 : ℝ) (501492591503/1000000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 5 (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 6 (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67105/524288 : ℝ))) 7 (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67105/524288 : ℝ)) hmem 8 (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67105/524288 : ℝ))) hcmem 8 (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67105/524288 : ℝ)) (496024121251/500000000000 : ℝ) (124006030313/125000000000 : ℝ) (62686573939/125000000000 : ℝ) (250746295761/500000000000 : ℝ) (198514217079/250000000000 : ℝ) (158811373667/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1032_exp_lower
  have heNumeric : (2054902117529/1000000000000 : ℝ)/4 ≤ Real.exp (-532852916543/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902117529/1000000000000 : ℝ)/4 ≤ Real.exp ((2097/16384 : ℝ)-(158811373667/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2097/16384 : ℝ) (67105/524288 : ℝ) (158811373667/200000000000 : ℝ) (2054902117529/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1033; no trusted numerical premise.
theorem cover8_leaf1033_exp_radius : (998002083850650911/1000000000000000000 : ℝ) ≤ Real.exp ((-33553/2097152 : ℝ)/8) ∧ Real.exp ((-33553/2097152 : ℝ)/8) ≤ (31187565120332841/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33553/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1033_exp_lower : (92011348085125867/100000000000000000 : ℝ) ≤ Real.exp ((-85256466221583/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256466221583/128000000000000 : ℝ)/8) ≤ (920113480851258671/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256466221583/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1033_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725531089/250000000000 : ℝ) ≤ 4*Real.exp (67105/524288 : ℝ)*Real.exp (-mu (radius 8 (33553/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725531089/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33553/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1033_exp_radius
  have hrNumeric : (984127992047/1000000000000 : ℝ) ≤ Real.exp (-33553/2097152 : ℝ) ∧ Real.exp (-33553/2097152 : ℝ) ≤ (61507999503/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984127992047/1000000000000 : ℝ) ≤ (radius 8 (33553/262144 : ℝ)) ∧ (radius 8 (33553/262144 : ℝ)) ≤ (61507999503/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33553/262144 : ℝ)) (984127992047/1000000000000 : ℝ) (61507999503/62500000000 : ℝ) (88730061517/500000000000 : ℝ) (177460123041/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33553/262144 : ℝ)) (984127992047/1000000000000 : ℝ) (61507999503/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984127992047/1000000000000 : ℝ) (61507999503/62500000000 : ℝ) (992063996023/1000000000000 : ℝ) (124007999503/125000000000 : ℝ) (992032253531/1000000000000 : ℝ) (992032253533/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 1 (992063996023/1000000000000 : ℝ) (124007999503/125000000000 : ℝ) (992032253531/1000000000000 : ℝ) (992032253533/1000000000000 : ℝ) (992048124777/1000000000000 : ℝ) (992048124779/1000000000000 : ℝ) (19840962493/20000000000 : ℝ) (248012031163/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 2 (992048124777/1000000000000 : ℝ) (992048124779/1000000000000 : ℝ) (19840962493/20000000000 : ℝ) (248012031163/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 3 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 4 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 5 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 6 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33553/262144 : ℝ)) 7 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33553/262144 : ℝ))) (88730061517/500000000000 : ℝ) (177460123041/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88730061517/500000000000 : ℝ) (177460123041/1000000000000 : ℝ) (588730061517/1000000000000 : ℝ) (588730061521/1000000000000 : ℝ) (105315040187/250000000000 : ℝ) (421260160757/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 1 (588730061517/1000000000000 : ℝ) (588730061521/1000000000000 : ℝ) (105315040187/250000000000 : ℝ) (421260160757/1000000000000 : ℝ) (126248777783/250000000000 : ℝ) (504995111139/1000000000000 : ℝ) (99600907697/200000000000 : ℝ) (498004538493/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 2 (126248777783/250000000000 : ℝ) (504995111139/1000000000000 : ℝ) (99600907697/200000000000 : ℝ) (498004538493/1000000000000 : ℝ) (62687478101/125000000000 : ℝ) (31343739051/62500000000 : ℝ) (501487644171/1000000000000 : ℝ) (501487644179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 3 (62687478101/125000000000 : ℝ) (31343739051/62500000000 : ℝ) (501487644171/1000000000000 : ℝ) (501487644179/1000000000000 : ℝ) (501493734489/1000000000000 : ℝ) (250746867249/500000000000 : ℝ) (125373433613/250000000000 : ℝ) (501493734461/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 4 (501493734489/1000000000000 : ℝ) (250746867249/500000000000 : ℝ) (125373433613/250000000000 : ℝ) (501493734461/1000000000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 5 (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 6 (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33553/262144 : ℝ))) 7 (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33553/262144 : ℝ)) hmem 8 (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33553/262144 : ℝ))) hcmem 8 (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33553/262144 : ℝ)) (992048124713/1000000000000 : ℝ) (248012031179/250000000000 : ℝ) (50149373447/100000000000 : ℝ) (6268671681/12500000000 : ℝ) (794058772341/1000000000000 : ℝ) (794058772361/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1033_exp_lower
  have heNumeric : (513725531089/250000000000 : ℝ)/4 ≤ Real.exp (-85256466221583/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725531089/250000000000 : ℝ)/4 ≤ Real.exp ((67105/524288 : ℝ)-(794058772361/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67105/524288 : ℝ) (33553/262144 : ℝ) (794058772361/1000000000000 : ℝ) (513725531089/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1034; no trusted numerical premise.
theorem cover8_leaf1034_exp_radius : (249500513526967877/250000000000000000 : ℝ) ≤ Real.exp ((-67107/4194304 : ℝ)/8) ∧ Real.exp ((-67107/4194304 : ℝ)/8) ≤ (998002054107871509/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67107/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1034_exp_lower : (230028370309157243/250000000000000000 : ℝ) ≤ Real.exp ((-42628232896351/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628232896351/64000000000000 : ℝ)/8) ≤ (920113481236628973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628232896351/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1034_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451065621/500000000000 : ℝ) ≤ 4*Real.exp (33553/262144 : ℝ)*Real.exp (-mu (radius 8 (67107/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451065621/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67107/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1034_exp_radius
  have hrNumeric : (984127757413/1000000000000 : ℝ) ≤ Real.exp (-67107/4194304 : ℝ) ∧ Real.exp (-67107/4194304 : ℝ) ≤ (492063878707/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984127757413/1000000000000 : ℝ) ≤ (radius 8 (67107/524288 : ℝ)) ∧ (radius 8 (67107/524288 : ℝ)) ≤ (492063878707/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67107/524288 : ℝ)) (984127757413/1000000000000 : ℝ) (492063878707/500000000000 : ℝ) (177461424223/1000000000000 : ℝ) (177461424229/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67107/524288 : ℝ)) (984127757413/1000000000000 : ℝ) (492063878707/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984127757413/1000000000000 : ℝ) (492063878707/500000000000 : ℝ) (496031939353/500000000000 : ℝ) (992063878707/1000000000000 : ℝ) (124004016909/125000000000 : ℝ) (992032135273/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 1 (496031939353/500000000000 : ℝ) (992063878707/1000000000000 : ℝ) (124004016909/125000000000 : ℝ) (992032135273/1000000000000 : ℝ) (992048006989/1000000000000 : ℝ) (99204800699/100000000000 : ℝ) (496024003431/500000000000 : ℝ) (62003000429/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 2 (992048006989/1000000000000 : ℝ) (99204800699/100000000000 : ℝ) (496024003431/500000000000 : ℝ) (62003000429/62500000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 3 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 4 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 5 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 6 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67107/524288 : ℝ)) 7 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67107/524288 : ℝ))) (177461424223/1000000000000 : ℝ) (177461424229/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177461424223/1000000000000 : ℝ) (177461424229/1000000000000 : ℝ) (588730712111/1000000000000 : ℝ) (117746142423/200000000000 : ℝ) (210630852573/500000000000 : ℝ) (210630852577/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 1 (588730712111/1000000000000 : ℝ) (117746142423/200000000000 : ℝ) (210630852573/500000000000 : ℝ) (210630852577/500000000000 : ℝ) (126249052157/250000000000 : ℝ) (100999241727/200000000000 : ℝ) (498005726529/1000000000000 : ℝ) (62250715817/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 2 (126249052157/250000000000 : ℝ) (100999241727/200000000000 : ℝ) (498005726529/1000000000000 : ℝ) (62250715817/125000000000 : ℝ) (250750483789/500000000000 : ℝ) (250750483793/500000000000 : ℝ) (125372196821/250000000000 : ℝ) (125372196823/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 3 (250750483789/500000000000 : ℝ) (250750483793/500000000000 : ℝ) (125372196821/250000000000 : ℝ) (125372196823/250000000000 : ℝ) (501494877431/1000000000000 : ℝ) (501494877439/1000000000000 : ℝ) (250747438697/500000000000 : ℝ) (501494877403/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 4 (501494877431/1000000000000 : ℝ) (501494877439/1000000000000 : ℝ) (250747438697/500000000000 : ℝ) (501494877403/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 5 (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 6 (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67107/524288 : ℝ))) 7 (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67107/524288 : ℝ)) hmem 8 (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67107/524288 : ℝ))) hcmem 8 (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67107/524288 : ℝ)) (39681920277/40000000000 : ℝ) (992048006927/1000000000000 : ℝ) (125373719353/250000000000 : ℝ) (501494877421/1000000000000 : ℝ) (794060676343/1000000000000 : ℝ) (794060676359/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1034_exp_lower
  have heNumeric : (1027451065621/500000000000 : ℝ)/4 ≤ Real.exp (-42628232896351/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451065621/500000000000 : ℝ)/4 ≤ Real.exp ((33553/262144 : ℝ)-(794060676359/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33553/262144 : ℝ) (67107/524288 : ℝ) (794060676359/1000000000000 : ℝ) (1027451065621/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1035; no trusted numerical premise.
theorem cover8_leaf1035_exp_radius : (998002024365092991/1000000000000000000 : ℝ) ≤ Real.exp ((-16777/1048576 : ℝ)/8) ∧ Real.exp ((-16777/1048576 : ℝ)/8) ≤ (7796890815352289/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-16777/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1035_exp_lower : (230028370405988629/250000000000000000 : ℝ) ≤ Real.exp ((-17051293072329/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051293072329/25600000000000 : ℝ)/8) ≤ (920113481623954517/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051293072329/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1035_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451069081/500000000000 : ℝ) ≤ 4*Real.exp (67107/524288 : ℝ)*Real.exp (-mu (radius 8 (16777/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451069081/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16777/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1035_exp_radius
  have hrNumeric : (984127522779/1000000000000 : ℝ) ≤ Real.exp (-16777/1048576 : ℝ) ∧ Real.exp (-16777/1048576 : ℝ) ≤ (49206376139/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984127522779/1000000000000 : ℝ) ≤ (radius 8 (16777/131072 : ℝ)) ∧ (radius 8 (16777/131072 : ℝ)) ≤ (49206376139/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16777/131072 : ℝ)) (984127522779/1000000000000 : ℝ) (49206376139/50000000000 : ℝ) (177462725401/1000000000000 : ℝ) (177462725407/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16777/131072 : ℝ)) (984127522779/1000000000000 : ℝ) (49206376139/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984127522779/1000000000000 : ℝ) (49206376139/50000000000 : ℝ) (992063761389/1000000000000 : ℝ) (99206376139/100000000000 : ℝ) (992032017013/1000000000000 : ℝ) (496016008507/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 1 (992063761389/1000000000000 : ℝ) (99206376139/100000000000 : ℝ) (992032017013/1000000000000 : ℝ) (496016008507/500000000000 : ℝ) (992047889201/1000000000000 : ℝ) (496023944601/500000000000 : ℝ) (496023944537/500000000000 : ℝ) (248011972269/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 2 (992047889201/1000000000000 : ℝ) (496023944601/500000000000 : ℝ) (496023944537/500000000000 : ℝ) (248011972269/250000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 3 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 4 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 5 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 6 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16777/131072 : ℝ)) 7 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16777/131072 : ℝ))) (177462725401/1000000000000 : ℝ) (177462725407/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177462725401/1000000000000 : ℝ) (177462725407/1000000000000 : ℝ) (5887313627/10000000000 : ℝ) (36795710169/62500000000 : ℝ) (16850529981/40000000000 : ℝ) (421263249533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 1 (5887313627/10000000000 : ℝ) (36795710169/62500000000 : ℝ) (16850529981/40000000000 : ℝ) (421263249533/1000000000000 : ℝ) (1972645727/3906250000 : ℝ) (504997306119/1000000000000 : ℝ) (249003457279/500000000000 : ℝ) (249003457283/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 2 (1972645727/3906250000 : ℝ) (504997306119/1000000000000 : ℝ) (249003457279/500000000000 : ℝ) (249003457283/500000000000 : ℝ) (100300422067/200000000000 : ℝ) (501502110343/1000000000000 : ℝ) (31343120649/62500000000 : ℝ) (62686241299/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 3 (100300422067/200000000000 : ℝ) (501502110343/1000000000000 : ℝ) (31343120649/62500000000 : ℝ) (62686241299/125000000000 : ℝ) (501496020359/1000000000000 : ℝ) (31343501273/62500000000 : ℝ) (250748010161/500000000000 : ℝ) (501496020331/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 4 (501496020359/1000000000000 : ℝ) (31343501273/62500000000 : ℝ) (250748010161/500000000000 : ℝ) (501496020331/1000000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 5 (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 6 (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16777/131072 : ℝ))) 7 (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16777/131072 : ℝ)) hmem 8 (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16777/131072 : ℝ))) hcmem 8 (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16777/131072 : ℝ)) (992047889137/1000000000000 : ℝ) (992047889139/1000000000000 : ℝ) (25074801017/50000000000 : ℝ) (10029920407/20000000000 : ℝ) (794062580321/1000000000000 : ℝ) (39703129017/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1035_exp_lower
  have heNumeric : (1027451069081/500000000000 : ℝ)/4 ≤ Real.exp (-17051293072329/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451069081/500000000000 : ℝ)/4 ≤ Real.exp ((67107/524288 : ℝ)-(39703129017/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67107/524288 : ℝ) (16777/131072 : ℝ) (39703129017/50000000000 : ℝ) (1027451069081/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1036; no trusted numerical premise.
theorem cover8_leaf1036_exp_radius : (998001994622315361/1000000000000000000 : ℝ) ≤ Real.exp ((-67109/4194304 : ℝ)/8) ∧ Real.exp ((-67109/4194304 : ℝ)/8) ≤ (499000997311157681/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67109/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1036_exp_lower : (92011348201346533/100000000000000000 : ℝ) ≤ Real.exp ((-21314116232039/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314116232039/32000000000000 : ℝ)/8) ≤ (920113482013465331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314116232039/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1036_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902145121/1000000000000 : ℝ) ≤ 4*Real.exp (16777/131072 : ℝ)*Real.exp (-mu (radius 8 (67109/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902145121/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67109/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1036_exp_radius
  have hrNumeric : (196825457629/200000000000 : ℝ) ≤ Real.exp (-67109/4194304 : ℝ) ∧ Real.exp (-67109/4194304 : ℝ) ≤ (492063644073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196825457629/200000000000 : ℝ) ≤ (radius 8 (67109/524288 : ℝ)) ∧ (radius 8 (67109/524288 : ℝ)) ≤ (492063644073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67109/524288 : ℝ)) (196825457629/200000000000 : ℝ) (492063644073/500000000000 : ℝ) (177464026569/1000000000000 : ℝ) (11091501661/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67109/524288 : ℝ)) (196825457629/200000000000 : ℝ) (492063644073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196825457629/200000000000 : ℝ) (492063644073/500000000000 : ℝ) (124007955509/125000000000 : ℝ) (992063644073/1000000000000 : ℝ) (992031898753/1000000000000 : ℝ) (198406379751/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 1 (124007955509/125000000000 : ℝ) (992063644073/1000000000000 : ℝ) (992031898753/1000000000000 : ℝ) (198406379751/200000000000 : ℝ) (248011942853/250000000000 : ℝ) (496023885707/500000000000 : ℝ) (198409554257/200000000000 : ℝ) (124005971411/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 2 (248011942853/250000000000 : ℝ) (496023885707/500000000000 : ℝ) (198409554257/200000000000 : ℝ) (124005971411/125000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 3 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 4 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 5 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 6 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67109/524288 : ℝ)) 7 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67109/524288 : ℝ))) (177464026569/1000000000000 : ℝ) (11091501661/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177464026569/1000000000000 : ℝ) (11091501661/62500000000 : ℝ) (147183003321/250000000000 : ℝ) (73591501661/125000000000 : ℝ) (421264793887/1000000000000 : ℝ) (52658099237/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 1 (147183003321/250000000000 : ℝ) (73591501661/125000000000 : ℝ) (421264793887/1000000000000 : ℝ) (52658099237/125000000000 : ℝ) (100999680717/200000000000 : ℝ) (63124800449/125000000000 : ℝ) (19920324103/40000000000 : ℝ) (498008102583/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 2 (100999680717/200000000000 : ℝ) (63124800449/125000000000 : ℝ) (19920324103/40000000000 : ℝ) (498008102583/1000000000000 : ℝ) (12537581327/25000000000 : ℝ) (15671976659/31250000000 : ℝ) (7835798023/15625000000 : ℝ) (501491073481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 3 (12537581327/25000000000 : ℝ) (15671976659/31250000000 : ℝ) (7835798023/15625000000 : ℝ) (501491073481/1000000000000 : ℝ) (125374290819/250000000000 : ℝ) (100299432657/200000000000 : ℝ) (501497163239/1000000000000 : ℝ) (31343572703/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 4 (125374290819/250000000000 : ℝ) (100299432657/200000000000 : ℝ) (501497163239/1000000000000 : ℝ) (31343572703/62500000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 5 (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 6 (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67109/524288 : ℝ))) 7 (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67109/524288 : ℝ)) hmem 8 (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67109/524288 : ℝ))) hcmem 8 (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67109/524288 : ℝ)) (248011942837/250000000000 : ℝ) (992047771351/1000000000000 : ℝ) (501497163257/1000000000000 : ℝ) (501497163267/1000000000000 : ℝ) (794064484283/1000000000000 : ℝ) (397032242151/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1036_exp_lower
  have heNumeric : (2054902145121/1000000000000 : ℝ)/4 ≤ Real.exp (-21314116232039/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902145121/1000000000000 : ℝ)/4 ≤ Real.exp ((16777/131072 : ℝ)-(397032242151/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16777/131072 : ℝ) (67109/524288 : ℝ) (397032242151/500000000000 : ℝ) (2054902145121/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1037; no trusted numerical premise.
theorem cover8_leaf1037_exp_radius : (124750245609942327/125000000000000000 : ℝ) ≤ Real.exp ((-33555/2097152 : ℝ)/8) ∧ Real.exp ((-33555/2097152 : ℝ)/8) ≤ (998001964879538617/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33555/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1037_exp_lower : (460056741202293171/500000000000000000 : ℝ) ≤ Real.exp ((-682051715943/1024000000000 : ℝ)/8) ∧ Real.exp ((-682051715943/1024000000000 : ℝ)/8) ≤ (920113482404586343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682051715943/1024000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1037_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902152109/1000000000000 : ℝ) ≤ 4*Real.exp (67109/524288 : ℝ)*Real.exp (-mu (radius 8 (33555/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902152109/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33555/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1037_exp_radius
  have hrNumeric : (98412705351/100000000000 : ℝ) ≤ Real.exp (-33555/2097152 : ℝ) ∧ Real.exp (-33555/2097152 : ℝ) ≤ (984127053511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98412705351/100000000000 : ℝ) ≤ (radius 8 (33555/262144 : ℝ)) ∧ (radius 8 (33555/262144 : ℝ)) ≤ (984127053511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33555/262144 : ℝ)) (98412705351/100000000000 : ℝ) (984127053511/1000000000000 : ℝ) (88732663867/500000000000 : ℝ) (8873266387/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33555/262144 : ℝ)) (98412705351/100000000000 : ℝ) (984127053511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98412705351/100000000000 : ℝ) (984127053511/1000000000000 : ℝ) (198412705351/200000000000 : ℝ) (248015881689/250000000000 : ℝ) (992031780493/1000000000000 : ℝ) (198406356099/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 1 (198412705351/200000000000 : ℝ) (248015881689/250000000000 : ℝ) (992031780493/1000000000000 : ℝ) (198406356099/200000000000 : ℝ) (124005956703/125000000000 : ℝ) (496023826813/500000000000 : ℝ) (992047653497/1000000000000 : ℝ) (992047653499/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 2 (124005956703/125000000000 : ℝ) (496023826813/500000000000 : ℝ) (992047653497/1000000000000 : ℝ) (992047653499/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 3 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 4 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 5 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 6 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33555/262144 : ℝ)) 7 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33555/262144 : ℝ))) (88732663867/500000000000 : ℝ) (8873266387/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88732663867/500000000000 : ℝ) (8873266387/50000000000 : ℝ) (588732663867/1000000000000 : ℝ) (58873266387/100000000000 : ℝ) (421266338239/1000000000000 : ℝ) (421266338247/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 1 (588732663867/1000000000000 : ℝ) (58873266387/100000000000 : ℝ) (421266338239/1000000000000 : ℝ) (421266338247/1000000000000 : ℝ) (504999501053/1000000000000 : ℝ) (504999501059/1000000000000 : ℝ) (62251161323/125000000000 : ℝ) (498009290591/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 2 (504999501053/1000000000000 : ℝ) (504999501059/1000000000000 : ℝ) (62251161323/125000000000 : ℝ) (498009290591/1000000000000 : ℝ) (250752197909/500000000000 : ℝ) (20060175833/40000000000 : ℝ) (250746108277/500000000000 : ℝ) (501492216561/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 3 (250752197909/500000000000 : ℝ) (20060175833/40000000000 : ℝ) (250746108277/500000000000 : ℝ) (501492216561/1000000000000 : ℝ) (250749153093/500000000000 : ℝ) (501498306193/1000000000000 : ℝ) (501498306149/1000000000000 : ℝ) (501498306157/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 4 (250749153093/500000000000 : ℝ) (501498306193/1000000000000 : ℝ) (501498306149/1000000000000 : ℝ) (501498306157/1000000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 5 (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 6 (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33555/262144 : ℝ))) 7 (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33555/262144 : ℝ)) hmem 8 (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33555/262144 : ℝ))) hcmem 8 (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33555/262144 : ℝ)) (24801191339/25000000000 : ℝ) (992047653563/1000000000000 : ℝ) (501498306167/1000000000000 : ℝ) (20059932247/40000000000 : ℝ) (397033194117/500000000000 : ℝ) (3176265553/4000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1037_exp_lower
  have heNumeric : (2054902152109/1000000000000 : ℝ)/4 ≤ Real.exp (-682051715943/1024000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902152109/1000000000000 : ℝ)/4 ≤ Real.exp ((67109/524288 : ℝ)-(3176265553/4000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67109/524288 : ℝ) (33555/262144 : ℝ) (3176265553/4000000000 : ℝ) (2054902152109/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1038; no trusted numerical premise.
theorem cover8_leaf1038_exp_radius : (998001935136762759/1000000000000000000 : ℝ) ≤ Real.exp ((-67111/4194304 : ℝ)/8) ∧ Real.exp ((-67111/4194304 : ℝ)/8) ≤ (24950048378419069/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67111/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1038_exp_lower : (920113482798237667/1000000000000000000 : ℝ) ≤ Real.exp ((-42628232027389/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628232027389/64000000000000 : ℝ)/8) ≤ (230028370699559417/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628232027389/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1038_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451079571/500000000000 : ℝ) ≤ 4*Real.exp (33555/262144 : ℝ)*Real.exp (-mu (radius 8 (67111/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451079571/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67111/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1038_exp_radius
  have hrNumeric : (246031704719/250000000000 : ℝ) ≤ Real.exp (-67111/4194304 : ℝ) ∧ Real.exp (-67111/4194304 : ℝ) ≤ (984126818877/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246031704719/250000000000 : ℝ) ≤ (radius 8 (67111/524288 : ℝ)) ∧ (radius 8 (67111/524288 : ℝ)) ≤ (984126818877/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67111/524288 : ℝ)) (246031704719/250000000000 : ℝ) (984126818877/1000000000000 : ℝ) (88733314441/500000000000 : ℝ) (177466628889/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67111/524288 : ℝ)) (246031704719/250000000000 : ℝ) (984126818877/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246031704719/250000000000 : ℝ) (984126818877/1000000000000 : ℝ) (496031704719/500000000000 : ℝ) (992063409439/1000000000000 : ℝ) (496015831117/500000000000 : ℝ) (248007915559/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 1 (496031704719/500000000000 : ℝ) (992063409439/1000000000000 : ℝ) (496015831117/500000000000 : ℝ) (248007915559/250000000000 : ℝ) (248011883959/250000000000 : ℝ) (496023767919/500000000000 : ℝ) (992047535709/1000000000000 : ℝ) (992047535711/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 2 (248011883959/250000000000 : ℝ) (496023767919/500000000000 : ℝ) (992047535709/1000000000000 : ℝ) (992047535711/1000000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 3 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 4 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 5 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 6 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67111/524288 : ℝ)) 7 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67111/524288 : ℝ))) (88733314441/500000000000 : ℝ) (177466628889/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88733314441/500000000000 : ℝ) (177466628889/1000000000000 : ℝ) (588733314441/1000000000000 : ℝ) (117746662889/200000000000 : ℝ) (210633941283/500000000000 : ℝ) (16850715303/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 1 (588733314441/1000000000000 : ℝ) (117746662889/200000000000 : ℝ) (210633941283/500000000000 : ℝ) (16850715303/40000000000 : ℝ) (505000598503/1000000000000 : ℝ) (50500059851/100000000000 : ℝ) (19920419143/40000000000 : ℝ) (498010478583/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 2 (505000598503/1000000000000 : ℝ) (50500059851/100000000000 : ℝ) (19920419143/40000000000 : ℝ) (498010478583/1000000000000 : ℝ) (501505538539/1000000000000 : ℝ) (501505538547/1000000000000 : ℝ) (250746679809/500000000000 : ℝ) (250746679813/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 3 (501505538539/1000000000000 : ℝ) (501505538547/1000000000000 : ℝ) (250746679809/500000000000 : ℝ) (250746679813/500000000000 : ℝ) (250749724539/500000000000 : ℝ) (501499449087/1000000000000 : ℝ) (501499449041/1000000000000 : ℝ) (10029988981/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 4 (250749724539/500000000000 : ℝ) (501499449087/1000000000000 : ℝ) (501499449041/1000000000000 : ℝ) (10029988981/20000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 5 (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 6 (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67111/524288 : ℝ))) 7 (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67111/524288 : ℝ)) hmem 8 (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67111/524288 : ℝ))) hcmem 8 (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67111/524288 : ℝ)) (248011883943/250000000000 : ℝ) (39681901431/40000000000 : ℝ) (501499449059/1000000000000 : ℝ) (501499449069/1000000000000 : ℝ) (794068292157/1000000000000 : ℝ) (49629268261/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1038_exp_lower
  have heNumeric : (1027451079571/500000000000 : ℝ)/4 ≤ Real.exp (-42628232027389/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451079571/500000000000 : ℝ)/4 ≤ Real.exp ((33555/262144 : ℝ)-(49629268261/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33555/262144 : ℝ) (67111/524288 : ℝ) (49629268261/62500000000 : ℝ) (1027451079571/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1039; no trusted numerical premise.
theorem cover8_leaf1039_exp_radius : (249500476348496947/250000000000000000 : ℝ) ≤ Real.exp ((-8389/524288 : ℝ)/8) ∧ Real.exp ((-8389/524288 : ℝ)/8) ≤ (998001905393987789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8389/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1039_exp_lower : (920113483194304289/1000000000000000000 : ℝ) ≤ Real.exp ((-85256463613993/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256463613993/128000000000000 : ℝ)/8) ≤ (92011348319430429/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256463613993/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1039_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451083109/500000000000 : ℝ) ≤ 4*Real.exp (67111/524288 : ℝ)*Real.exp (-mu (radius 8 (8389/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451083109/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8389/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1039_exp_radius
  have hrNumeric : (492063292121/500000000000 : ℝ) ≤ Real.exp (-8389/524288 : ℝ) ∧ Real.exp (-8389/524288 : ℝ) ≤ (984126584243/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492063292121/500000000000 : ℝ) ≤ (radius 8 (8389/65536 : ℝ)) ∧ (radius 8 (8389/65536 : ℝ)) ≤ (984126584243/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8389/65536 : ℝ)) (492063292121/500000000000 : ℝ) (984126584243/1000000000000 : ℝ) (177467930021/1000000000000 : ℝ) (44366982507/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8389/65536 : ℝ)) (492063292121/500000000000 : ℝ) (984126584243/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492063292121/500000000000 : ℝ) (984126584243/1000000000000 : ℝ) (992063292121/1000000000000 : ℝ) (496031646061/500000000000 : ℝ) (39681261759/40000000000 : ℝ) (124003942997/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 1 (992063292121/1000000000000 : ℝ) (496031646061/500000000000 : ℝ) (39681261759/40000000000 : ℝ) (124003942997/125000000000 : ℝ) (15500740907/15625000000 : ℝ) (992047418049/1000000000000 : ℝ) (3100148181/3125000000 : ℝ) (496023708961/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 2 (15500740907/15625000000 : ℝ) (992047418049/1000000000000 : ℝ) (3100148181/3125000000 : ℝ) (496023708961/500000000000 : ℝ) (7750370453/7812500000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 3 (7750370453/7812500000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 4 (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 5 (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 6 (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8389/65536 : ℝ)) 7 (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8389/65536 : ℝ))) (177467930021/1000000000000 : ℝ) (44366982507/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177467930021/1000000000000 : ℝ) (44366982507/250000000000 : ℝ) (58873396501/100000000000 : ℝ) (294366982507/500000000000 : ℝ) (105317356719/250000000000 : ℝ) (84253885377/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 1 (58873396501/100000000000 : ℝ) (294366982507/500000000000 : ℝ) (105317356719/250000000000 : ℝ) (84253885377/200000000000 : ℝ) (505001695943/1000000000000 : ℝ) (10100033919/20000000000 : ℝ) (62251458319/125000000000 : ℝ) (778143229/1562500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 2 (505001695943/1000000000000 : ℝ) (10100033919/20000000000 : ℝ) (62251458319/125000000000 : ℝ) (778143229/1562500000 : ℝ) (501506681247/1000000000000 : ℝ) (100301336251/200000000000 : ℝ) (501494502669/1000000000000 : ℝ) (250747251339/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 3 (501506681247/1000000000000 : ℝ) (100301336251/200000000000 : ℝ) (501494502669/1000000000000 : ℝ) (250747251339/500000000000 : ℝ) (250750295979/500000000000 : ℝ) (501500591967/1000000000000 : ℝ) (501500591921/1000000000000 : ℝ) (50150059193/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 4 (250750295979/500000000000 : ℝ) (501500591967/1000000000000 : ℝ) (501500591921/1000000000000 : ℝ) (50150059193/100000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 5 (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 6 (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8389/65536 : ℝ))) 7 (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8389/65536 : ℝ)) hmem 8 (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8389/65536 : ℝ))) hcmem 8 (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8389/65536 : ℝ)) (992047417983/1000000000000 : ℝ) (496023708993/500000000000 : ℝ) (501500591939/1000000000000 : ℝ) (501500591949/1000000000000 : ℝ) (397035098031/500000000000 : ℝ) (794070196081/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1039_exp_lower
  have heNumeric : (1027451083109/500000000000 : ℝ)/4 ≤ Real.exp (-85256463613993/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451083109/500000000000 : ℝ)/4 ≤ Real.exp ((67111/524288 : ℝ)-(794070196081/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67111/524288 : ℝ) (8389/65536 : ℝ) (794070196081/1000000000000 : ℝ) (1027451083109/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1040; no trusted numerical premise.
theorem cover8_leaf1040_exp_radius : (998001875651213703/1000000000000000000 : ℝ) ≤ Real.exp ((-67113/4194304 : ℝ)/8) ∧ Real.exp ((-67113/4194304 : ℝ)/8) ≤ (124750234456401713/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67113/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1040_exp_lower : (460056741796278091/500000000000000000 : ℝ) ≤ Real.exp ((-10657057896347/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657057896347/16000000000000 : ℝ)/8) ≤ (920113483592556183/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657057896347/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1040_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451086667/500000000000 : ℝ) ≤ 4*Real.exp (8389/65536 : ℝ)*Real.exp (-mu (radius 8 (67113/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451086667/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67113/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1040_exp_radius
  have hrNumeric : (123015793701/125000000000 : ℝ) ≤ Real.exp (-67113/4194304 : ℝ) ∧ Real.exp (-67113/4194304 : ℝ) ≤ (984126349609/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123015793701/125000000000 : ℝ) ≤ (radius 8 (67113/524288 : ℝ)) ∧ (radius 8 (67113/524288 : ℝ)) ≤ (984126349609/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67113/524288 : ℝ)) (123015793701/125000000000 : ℝ) (984126349609/1000000000000 : ℝ) (3549384623/20000000000 : ℝ) (177469231157/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67113/524288 : ℝ)) (123015793701/125000000000 : ℝ) (984126349609/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123015793701/125000000000 : ℝ) (984126349609/1000000000000 : ℝ) (248015793701/250000000000 : ℝ) (198412634961/200000000000 : ℝ) (198406285143/200000000000 : ℝ) (992031425717/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 1 (248015793701/250000000000 : ℝ) (198412634961/200000000000 : ℝ) (198406285143/200000000000 : ℝ) (992031425717/1000000000000 : ℝ) (992047300259/1000000000000 : ℝ) (992047300261/1000000000000 : ℝ) (248011825033/250000000000 : ℝ) (496023650067/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 2 (992047300259/1000000000000 : ℝ) (992047300261/1000000000000 : ℝ) (248011825033/250000000000 : ℝ) (496023650067/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 3 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 4 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 5 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 6 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67113/524288 : ℝ)) 7 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67113/524288 : ℝ))) (3549384623/20000000000 : ℝ) (177469231157/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3549384623/20000000000 : ℝ) (177469231157/1000000000000 : ℝ) (23549384623/40000000000 : ℝ) (588734615579/1000000000000 : ℝ) (421270971169/1000000000000 : ℝ) (210635485589/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 1 (23549384623/40000000000 : ℝ) (588734615579/1000000000000 : ℝ) (421270971169/1000000000000 : ℝ) (210635485589/500000000000 : ℝ) (126250698343/250000000000 : ℝ) (505002793379/1000000000000 : ℝ) (124503213629/250000000000 : ℝ) (124503213631/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 2 (126250698343/250000000000 : ℝ) (505002793379/1000000000000 : ℝ) (124503213629/250000000000 : ℝ) (124503213631/250000000000 : ℝ) (62688477993/125000000000 : ℝ) (31344238997/62500000000 : ℝ) (501495645709/1000000000000 : ℝ) (250747822859/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 3 (62688477993/125000000000 : ℝ) (31344238997/62500000000 : ℝ) (501495645709/1000000000000 : ℝ) (250747822859/500000000000 : ℝ) (250750867413/500000000000 : ℝ) (100300346967/200000000000 : ℝ) (501501734789/1000000000000 : ℝ) (501501734799/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 4 (250750867413/500000000000 : ℝ) (100300346967/200000000000 : ℝ) (501501734789/1000000000000 : ℝ) (501501734799/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 5 (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 6 (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67113/524288 : ℝ))) 7 (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67113/524288 : ℝ)) hmem 8 (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67113/524288 : ℝ))) hcmem 8 (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67113/524288 : ℝ)) (198409460039/200000000000 : ℝ) (496023650099/500000000000 : ℝ) (501501734807/1000000000000 : ℝ) (501501734817/1000000000000 : ℝ) (198518024987/250000000000 : ℝ) (794072099967/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1040_exp_lower
  have heNumeric : (1027451086667/500000000000 : ℝ)/4 ≤ Real.exp (-10657057896347/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451086667/500000000000 : ℝ)/4 ≤ Real.exp ((8389/65536 : ℝ)-(794072099967/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8389/65536 : ℝ) (67113/524288 : ℝ) (794072099967/1000000000000 : ℝ) (1027451086667/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1041; no trusted numerical premise.
theorem cover8_leaf1041_exp_radius : (124750230738555063/125000000000000000 : ℝ) ≤ Real.exp ((-33557/2097152 : ℝ)/8) ∧ Real.exp ((-33557/2097152 : ℝ)/8) ≤ (199600369181688101/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33557/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1041_exp_lower : (14376773187390521/15625000000000000 : ℝ) ≤ Real.exp ((-85256462725127/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256462725127/128000000000000 : ℝ)/8) ≤ (184022696798598669/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256462725127/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1041_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862772561/125000000000 : ℝ) ≤ 4*Real.exp (67113/524288 : ℝ)*Real.exp (-mu (radius 8 (33557/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862772561/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33557/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1041_exp_radius
  have hrNumeric : (492063057487/500000000000 : ℝ) ≤ Real.exp (-33557/2097152 : ℝ) ∧ Real.exp (-33557/2097152 : ℝ) ≤ (39365044599/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492063057487/500000000000 : ℝ) ≤ (radius 8 (33557/262144 : ℝ)) ∧ (radius 8 (33557/262144 : ℝ)) ≤ (39365044599/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33557/262144 : ℝ)) (492063057487/500000000000 : ℝ) (39365044599/40000000000 : ℝ) (17747053227/100000000000 : ℝ) (44367633069/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33557/262144 : ℝ)) (492063057487/500000000000 : ℝ) (39365044599/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492063057487/500000000000 : ℝ) (39365044599/40000000000 : ℝ) (992063057487/1000000000000 : ℝ) (62003941093/62500000000 : ℝ) (15500489179/15625000000 : ℝ) (496015653729/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 1 (992063057487/1000000000000 : ℝ) (62003941093/62500000000 : ℝ) (15500489179/15625000000 : ℝ) (496015653729/500000000000 : ℝ) (992047182471/1000000000000 : ℝ) (992047182473/1000000000000 : ℝ) (124005897793/125000000000 : ℝ) (496023591173/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 2 (992047182471/1000000000000 : ℝ) (992047182473/1000000000000 : ℝ) (124005897793/125000000000 : ℝ) (496023591173/500000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 3 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 4 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 5 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 6 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33557/262144 : ℝ)) 7 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33557/262144 : ℝ))) (17747053227/100000000000 : ℝ) (44367633069/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17747053227/100000000000 : ℝ) (44367633069/250000000000 : ℝ) (117747053227/200000000000 : ℝ) (294367633069/500000000000 : ℝ) (84254503089/200000000000 : ℝ) (421272515453/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 1 (117747053227/200000000000 : ℝ) (294367633069/500000000000 : ℝ) (84254503089/200000000000 : ℝ) (421272515453/1000000000000 : ℝ) (50500389079/100000000000 : ℝ) (126250972699/250000000000 : ℝ) (124503510617/250000000000 : ℝ) (19920561699/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 2 (50500389079/100000000000 : ℝ) (126250972699/250000000000 : ℝ) (124503510617/250000000000 : ℝ) (19920561699/40000000000 : ℝ) (501508966629/1000000000000 : ℝ) (125377241659/250000000000 : ℝ) (501496788737/1000000000000 : ℝ) (100299357749/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 3 (501508966629/1000000000000 : ℝ) (125377241659/250000000000 : ℝ) (501496788737/1000000000000 : ℝ) (100299357749/200000000000 : ℝ) (501502877683/1000000000000 : ℝ) (501502877691/1000000000000 : ℝ) (250751438823/500000000000 : ℝ) (250751438827/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 4 (501502877683/1000000000000 : ℝ) (501502877691/1000000000000 : ℝ) (250751438823/500000000000 : ℝ) (250751438827/500000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 5 (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 6 (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33557/262144 : ℝ))) 7 (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33557/262144 : ℝ)) hmem 8 (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33557/262144 : ℝ))) hcmem 8 (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33557/262144 : ℝ)) (992047182407/1000000000000 : ℝ) (99204718241/100000000000 : ℝ) (15671964927/31250000000 : ℝ) (501502877673/1000000000000 : ℝ) (99259250477/125000000000 : ℝ) (397037001917/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1041_exp_lower
  have heNumeric : (256862772561/125000000000 : ℝ)/4 ≤ Real.exp (-85256462725127/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862772561/125000000000 : ℝ)/4 ≤ Real.exp ((67113/524288 : ℝ)-(397037001917/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67113/524288 : ℝ) (33557/262144 : ℝ) (397037001917/500000000000 : ℝ) (256862772561/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1042; no trusted numerical premise.
theorem cover8_leaf1042_exp_radius : (31187556755177131/31250000000000000 : ℝ) ≤ Real.exp ((-67115/4194304 : ℝ)/8) ∧ Real.exp ((-67115/4194304 : ℝ)/8) ≤ (998001816165668193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67115/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1042_exp_lower : (92011348439573079/100000000000000000 : ℝ) ≤ Real.exp ((-42628231138459/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628231138459/64000000000000 : ℝ)/8) ≤ (920113484395730791/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628231138459/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1042_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725546921/250000000000 : ℝ) ≤ 4*Real.exp (33557/262144 : ℝ)*Real.exp (-mu (radius 8 (67115/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725546921/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67115/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1042_exp_radius
  have hrNumeric : (49206294017/50000000000 : ℝ) ≤ Real.exp (-67115/4194304 : ℝ) ∧ Real.exp (-67115/4194304 : ℝ) ≤ (984125880341/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49206294017/50000000000 : ℝ) ≤ (radius 8 (67115/524288 : ℝ)) ∧ (radius 8 (67115/524288 : ℝ)) ≤ (984125880341/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67115/524288 : ℝ)) (49206294017/50000000000 : ℝ) (984125880341/1000000000000 : ℝ) (177471833379/1000000000000 : ℝ) (35494366677/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67115/524288 : ℝ)) (49206294017/50000000000 : ℝ) (984125880341/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49206294017/50000000000 : ℝ) (984125880341/1000000000000 : ℝ) (99206294017/100000000000 : ℝ) (992062940171/1000000000000 : ℝ) (992031189197/1000000000000 : ℝ) (496015594599/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 1 (99206294017/100000000000 : ℝ) (992062940171/1000000000000 : ℝ) (992031189197/1000000000000 : ℝ) (496015594599/500000000000 : ℝ) (992047064683/1000000000000 : ℝ) (198409412937/200000000000 : ℝ) (248011766139/250000000000 : ℝ) (496023532279/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 2 (992047064683/1000000000000 : ℝ) (198409412937/200000000000 : ℝ) (248011766139/250000000000 : ℝ) (496023532279/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 3 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 4 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 5 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 6 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67115/524288 : ℝ)) 7 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67115/524288 : ℝ))) (177471833379/1000000000000 : ℝ) (35494366677/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177471833379/1000000000000 : ℝ) (35494366677/200000000000 : ℝ) (588735916689/1000000000000 : ℝ) (588735916693/1000000000000 : ℝ) (421274059703/1000000000000 : ℝ) (421274059711/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 1 (588735916689/1000000000000 : ℝ) (588735916693/1000000000000 : ℝ) (421274059703/1000000000000 : ℝ) (421274059711/1000000000000 : ℝ) (126251247049/250000000000 : ℝ) (252502494101/500000000000 : ℝ) (249007615203/500000000000 : ℝ) (498015230413/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 2 (126251247049/250000000000 : ℝ) (252502494101/500000000000 : ℝ) (249007615203/500000000000 : ℝ) (498015230413/1000000000000 : ℝ) (501510109301/1000000000000 : ℝ) (125377527327/250000000000 : ℝ) (501497931753/1000000000000 : ℝ) (6268724147/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 3 (501510109301/1000000000000 : ℝ) (125377527327/250000000000 : ℝ) (501497931753/1000000000000 : ℝ) (6268724147/12500000000 : ℝ) (501504020527/1000000000000 : ℝ) (250752010267/500000000000 : ℝ) (50150402049/100000000000 : ℝ) (250752010249/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 4 (501504020527/1000000000000 : ℝ) (250752010267/500000000000 : ℝ) (50150402049/100000000000 : ℝ) (250752010249/500000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 5 (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 6 (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67115/524288 : ℝ))) 7 (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67115/524288 : ℝ)) hmem 8 (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67115/524288 : ℝ))) hcmem 8 (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67115/524288 : ℝ)) (992047064619/1000000000000 : ℝ) (496023532311/500000000000 : ℝ) (125376005127/250000000000 : ℝ) (125376005129/250000000000 : ℝ) (158815181533/200000000000 : ℝ) (794075907681/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1042_exp_lower
  have heNumeric : (513725546921/250000000000 : ℝ)/4 ≤ Real.exp (-42628231138459/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725546921/250000000000 : ℝ)/4 ≤ Real.exp ((33557/262144 : ℝ)-(794075907681/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33557/262144 : ℝ) (67115/524288 : ℝ) (794075907681/1000000000000 : ℝ) (513725546921/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1043; no trusted numerical premise.
theorem cover8_leaf1043_exp_radius : (499000893211448383/500000000000000000 : ℝ) ≤ Real.exp ((-16779/1048576 : ℝ)/8) ∧ Real.exp ((-16779/1048576 : ℝ)/8) ≤ (998001786422896767/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16779/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1043_exp_lower : (920113484800308463/1000000000000000000 : ℝ) ≤ Real.exp ((-85256461826661/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256461826661/128000000000000 : ℝ)/8) ≤ (57507092800019279/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256461826661/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1043_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215693591/31250000000 : ℝ) ≤ 4*Real.exp (67115/524288 : ℝ)*Real.exp (-mu (radius 8 (16779/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215693591/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16779/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1043_exp_radius
  have hrNumeric : (492062822853/500000000000 : ℝ) ≤ Real.exp (-16779/1048576 : ℝ) ∧ Real.exp (-16779/1048576 : ℝ) ≤ (984125645707/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492062822853/500000000000 : ℝ) ≤ (radius 8 (16779/131072 : ℝ)) ∧ (radius 8 (16779/131072 : ℝ)) ≤ (984125645707/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16779/131072 : ℝ)) (492062822853/500000000000 : ℝ) (984125645707/1000000000000 : ℝ) (88736567239/500000000000 : ℝ) (35494626897/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16779/131072 : ℝ)) (492062822853/500000000000 : ℝ) (984125645707/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492062822853/500000000000 : ℝ) (984125645707/1000000000000 : ℝ) (992062822853/1000000000000 : ℝ) (496031411427/500000000000 : ℝ) (992031070937/1000000000000 : ℝ) (992031070939/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 1 (992062822853/1000000000000 : ℝ) (496031411427/500000000000 : ℝ) (992031070937/1000000000000 : ℝ) (992031070939/1000000000000 : ℝ) (198409389379/200000000000 : ℝ) (992046946897/1000000000000 : ℝ) (992046946767/1000000000000 : ℝ) (99204694677/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 2 (198409389379/200000000000 : ℝ) (992046946897/1000000000000 : ℝ) (992046946767/1000000000000 : ℝ) (99204694677/100000000000 : ℝ) (992046946831/1000000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 3 (992046946831/1000000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 4 (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 5 (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 6 (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16779/131072 : ℝ)) 7 (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16779/131072 : ℝ))) (88736567239/500000000000 : ℝ) (35494626897/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88736567239/500000000000 : ℝ) (35494626897/200000000000 : ℝ) (588736567239/1000000000000 : ℝ) (588736567243/1000000000000 : ℝ) (421275603943/1000000000000 : ℝ) (26329725247/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 1 (588736567239/1000000000000 : ℝ) (588736567243/1000000000000 : ℝ) (421275603943/1000000000000 : ℝ) (26329725247/62500000000 : ℝ) (505006085591/1000000000000 : ℝ) (252503042799/500000000000 : ℝ) (49801641833/100000000000 : ℝ) (249008209169/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 2 (505006085591/1000000000000 : ℝ) (252503042799/500000000000 : ℝ) (49801641833/100000000000 : ℝ) (249008209169/500000000000 : ℝ) (12537781299/25000000000 : ℝ) (244878541/488281250 : ℝ) (100299814951/200000000000 : ℝ) (125374768691/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 3 (12537781299/25000000000 : ℝ) (244878541/488281250 : ℝ) (100299814951/200000000000 : ℝ) (125374768691/250000000000 : ℝ) (501505163357/1000000000000 : ℝ) (250752581683/500000000000 : ℝ) (12537629083/25000000000 : ℝ) (50150516333/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 4 (501505163357/1000000000000 : ℝ) (250752581683/500000000000 : ℝ) (12537629083/25000000000 : ℝ) (50150516333/100000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 5 (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 6 (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16779/131072 : ℝ))) 7 (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16779/131072 : ℝ)) hmem 8 (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16779/131072 : ℝ))) hcmem 8 (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16779/131072 : ℝ)) (99204694683/100000000000 : ℝ) (496023473417/500000000000 : ℝ) (250752581669/500000000000 : ℝ) (125376290837/250000000000 : ℝ) (198519452873/250000000000 : ℝ) (99259726439/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1043_exp_lower
  have heNumeric : (64215693591/31250000000 : ℝ)/4 ≤ Real.exp (-85256461826661/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215693591/31250000000 : ℝ)/4 ≤ Real.exp ((67115/524288 : ℝ)-(99259726439/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67115/524288 : ℝ) (16779/131072 : ℝ) (99259726439/125000000000 : ℝ) (64215693591/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1044; no trusted numerical premise.
theorem cover8_leaf1044_exp_radius : (998001756680126227/1000000000000000000 : ℝ) ≤ Real.exp ((-67117/4194304 : ℝ)/8) ∧ Real.exp ((-67117/4194304 : ℝ)/8) ≤ (249500439170031557/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67117/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1044_exp_lower : (184022697041414281/200000000000000000 : ℝ) ≤ Real.exp ((-21314115343493/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314115343493/32000000000000 : ℝ)/8) ≤ (460056742603535703/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314115343493/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1044_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745110109/50000000000 : ℝ) ≤ 4*Real.exp (16779/131072 : ℝ)*Real.exp (-mu (radius 8 (67117/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745110109/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67117/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1044_exp_radius
  have hrNumeric : (3844239887/3906250000 : ℝ) ≤ Real.exp (-67117/4194304 : ℝ) ∧ Real.exp (-67117/4194304 : ℝ) ≤ (984125411073/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3844239887/3906250000 : ℝ) ≤ (radius 8 (67117/524288 : ℝ)) ∧ (radius 8 (67117/524288 : ℝ)) ≤ (984125411073/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67117/524288 : ℝ)) (3844239887/3906250000 : ℝ) (984125411073/1000000000000 : ℝ) (11092152223/62500000000 : ℝ) (7098977423/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67117/524288 : ℝ)) (3844239887/3906250000 : ℝ) (984125411073/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3844239887/3906250000 : ℝ) (984125411073/1000000000000 : ℝ) (7750489887/7812500000 : ℝ) (992062705537/1000000000000 : ℝ) (496015476339/500000000000 : ℝ) (992030952679/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 1 (7750489887/7812500000 : ℝ) (992062705537/1000000000000 : ℝ) (496015476339/500000000000 : ℝ) (992030952679/1000000000000 : ℝ) (992046829107/1000000000000 : ℝ) (248011707277/250000000000 : ℝ) (992046828979/1000000000000 : ℝ) (992046828981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 2 (992046829107/1000000000000 : ℝ) (248011707277/250000000000 : ℝ) (992046828979/1000000000000 : ℝ) (992046828981/1000000000000 : ℝ) (992046829043/1000000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 3 (992046829043/1000000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 4 (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 5 (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 6 (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67117/524288 : ℝ)) 7 (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67117/524288 : ℝ))) (11092152223/62500000000 : ℝ) (7098977423/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11092152223/62500000000 : ℝ) (7098977423/40000000000 : ℝ) (73592152223/125000000000 : ℝ) (147184304447/250000000000 : ℝ) (421277148167/1000000000000 : ℝ) (26329821761/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 1 (73592152223/125000000000 : ℝ) (147184304447/250000000000 : ℝ) (421277148167/1000000000000 : ℝ) (26329821761/62500000000 : ℝ) (20200287319/40000000000 : ℝ) (252503591491/500000000000 : ℝ) (249008803121/500000000000 : ℝ) (79682817/160000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 2 (20200287319/40000000000 : ℝ) (252503591491/500000000000 : ℝ) (249008803121/500000000000 : ℝ) (79682817/160000000 : ℝ) (31344524663/62500000000 : ℝ) (62689049327/125000000000 : ℝ) (250750108873/500000000000 : ℝ) (100300043551/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 3 (31344524663/62500000000 : ℝ) (62689049327/125000000000 : ℝ) (250750108873/500000000000 : ℝ) (100300043551/200000000000 : ℝ) (501506306177/1000000000000 : ℝ) (250753153093/500000000000 : ℝ) (25075315307/50000000000 : ℝ) (501506306149/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 4 (501506306177/1000000000000 : ℝ) (250753153093/500000000000 : ℝ) (25075315307/50000000000 : ℝ) (501506306149/1000000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 5 (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 6 (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67117/524288 : ℝ))) 7 (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67117/524288 : ℝ)) hmem 8 (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67117/524288 : ℝ))) hcmem 8 (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67117/524288 : ℝ)) (496023414521/500000000000 : ℝ) (198409365809/200000000000 : ℝ) (250753153079/500000000000 : ℝ) (62688288271/125000000000 : ℝ) (158815943061/200000000000 : ℝ) (198519928831/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1044_exp_lower
  have heNumeric : (102745110109/50000000000 : ℝ)/4 ≤ Real.exp (-21314115343493/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745110109/50000000000 : ℝ)/4 ≤ Real.exp ((16779/131072 : ℝ)-(198519928831/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16779/131072 : ℝ) (67117/524288 : ℝ) (198519928831/250000000000 : ℝ) (102745110109/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1045; no trusted numerical premise.
theorem cover8_leaf1045_exp_radius : (499000863468678287/500000000000000000 : ℝ) ≤ Real.exp ((-33559/2097152 : ℝ)/8) ∧ Real.exp ((-33559/2097152 : ℝ)/8) ≤ (39920069077494263/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33559/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1045_exp_lower : (460056742808527373/500000000000000000 : ℝ) ≤ Real.exp ((-85256460917699/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256460917699/128000000000000 : ℝ)/8) ≤ (920113485617054747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256460917699/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1045_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980441901/200000000000 : ℝ) ≤ 4*Real.exp (67117/524288 : ℝ)*Real.exp (-mu (radius 8 (33559/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980441901/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33559/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1045_exp_radius
  have hrNumeric : (984125176439/1000000000000 : ℝ) ≤ Real.exp (-33559/2097152 : ℝ) ∧ Real.exp (-33559/2097152 : ℝ) ≤ (24603129411/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984125176439/1000000000000 : ℝ) ≤ (radius 8 (33559/262144 : ℝ)) ∧ (radius 8 (33559/262144 : ℝ)) ≤ (24603129411/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33559/262144 : ℝ)) (984125176439/1000000000000 : ℝ) (24603129411/25000000000 : ℝ) (88737868321/500000000000 : ℝ) (177475736649/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33559/262144 : ℝ)) (984125176439/1000000000000 : ℝ) (24603129411/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984125176439/1000000000000 : ℝ) (24603129411/25000000000 : ℝ) (992062588219/1000000000000 : ℝ) (49603129411/50000000000 : ℝ) (992030834419/1000000000000 : ℝ) (49601541721/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 1 (992062588219/1000000000000 : ℝ) (49603129411/50000000000 : ℝ) (992030834419/1000000000000 : ℝ) (49601541721/50000000000 : ℝ) (992046711319/1000000000000 : ℝ) (24801167783/25000000000 : ℝ) (992046711191/1000000000000 : ℝ) (992046711193/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 2 (992046711319/1000000000000 : ℝ) (24801167783/25000000000 : ℝ) (992046711191/1000000000000 : ℝ) (992046711193/1000000000000 : ℝ) (198409342251/200000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 3 (198409342251/200000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 4 (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 5 (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 6 (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33559/262144 : ℝ)) 7 (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33559/262144 : ℝ))) (88737868321/500000000000 : ℝ) (177475736649/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88737868321/500000000000 : ℝ) (177475736649/1000000000000 : ℝ) (588737868321/1000000000000 : ℝ) (23549514733/40000000000 : ℝ) (210639346183/500000000000 : ℝ) (3370229539/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 1 (588737868321/1000000000000 : ℝ) (23549514733/40000000000 : ℝ) (210639346183/500000000000 : ℝ) (3370229539/8000000000 : ℝ) (505008280343/1000000000000 : ℝ) (10100165607/20000000000 : ℝ) (99603758827/200000000000 : ℝ) (498018794143/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 2 (505008280343/1000000000000 : ℝ) (10100165607/20000000000 : ℝ) (99603758827/200000000000 : ℝ) (498018794143/1000000000000 : ℝ) (501513537239/1000000000000 : ℝ) (501513537247/1000000000000 : ℝ) (6268767009/12500000000 : ℝ) (501501360729/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 3 (501513537239/1000000000000 : ℝ) (501513537247/1000000000000 : ℝ) (6268767009/12500000000 : ℝ) (501501360729/1000000000000 : ℝ) (501507448979/1000000000000 : ℝ) (125376862247/250000000000 : ℝ) (250753724471/500000000000 : ℝ) (62688431119/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 4 (501507448979/1000000000000 : ℝ) (125376862247/250000000000 : ℝ) (250753724471/500000000000 : ℝ) (62688431119/125000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 5 (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 6 (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33559/262144 : ℝ))) 7 (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33559/262144 : ℝ)) hmem 8 (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33559/262144 : ℝ))) hcmem 8 (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33559/262144 : ℝ)) (496023355627/500000000000 : ℝ) (992046711257/1000000000000 : ℝ) (783605389/1562500000 : ℝ) (50150744897/100000000000 : ℝ) (49630101193/62500000000 : ℝ) (198520404777/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1045_exp_lower
  have heNumeric : (410980441901/200000000000 : ℝ)/4 ≤ Real.exp (-85256460917699/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980441901/200000000000 : ℝ)/4 ≤ Real.exp ((67117/524288 : ℝ)-(198520404777/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67117/524288 : ℝ) (33559/262144 : ℝ) (198520404777/250000000000 : ℝ) (410980441901/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1046; no trusted numerical premise.
theorem cover8_leaf1046_exp_radius : (31187553037330869/31250000000000000 : ℝ) ≤ Real.exp ((-67119/4194304 : ℝ)/8) ∧ Real.exp ((-67119/4194304 : ℝ)/8) ≤ (998001697194587809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67119/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1046_exp_lower : (230028371507047057/250000000000000000 : ℝ) ≤ Real.exp ((-42628230230073/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628230230073/64000000000000 : ℝ)/8) ≤ (920113486028188229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628230230073/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1046_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098044337/20000000000 : ℝ) ≤ 4*Real.exp (33559/262144 : ℝ)*Real.exp (-mu (radius 8 (67119/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (41098044337/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67119/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1046_exp_radius
  have hrNumeric : (196824988361/200000000000 : ℝ) ≤ Real.exp (-67119/4194304 : ℝ) ∧ Real.exp (-67119/4194304 : ℝ) ≤ (492062470903/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196824988361/200000000000 : ℝ) ≤ (radius 8 (67119/524288 : ℝ)) ∧ (radius 8 (67119/524288 : ℝ)) ≤ (492062470903/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67119/524288 : ℝ)) (196824988361/200000000000 : ℝ) (492062470903/500000000000 : ℝ) (11092314857/62500000000 : ℝ) (177477037719/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67119/524288 : ℝ)) (196824988361/200000000000 : ℝ) (492062470903/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196824988361/200000000000 : ℝ) (492062470903/500000000000 : ℝ) (496031235451/500000000000 : ℝ) (992062470903/1000000000000 : ℝ) (775023997/781250000 : ℝ) (992030716161/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 1 (496031235451/500000000000 : ℝ) (992062470903/1000000000000 : ℝ) (775023997/781250000 : ℝ) (992030716161/1000000000000 : ℝ) (992046593531/1000000000000 : ℝ) (248011648383/250000000000 : ℝ) (992046593403/1000000000000 : ℝ) (198409318681/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 2 (992046593531/1000000000000 : ℝ) (248011648383/250000000000 : ℝ) (992046593403/1000000000000 : ℝ) (198409318681/200000000000 : ℝ) (992046593467/1000000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 3 (992046593467/1000000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 4 (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 5 (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 6 (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67119/524288 : ℝ)) 7 (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67119/524288 : ℝ))) (11092314857/62500000000 : ℝ) (177477037719/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11092314857/62500000000 : ℝ) (177477037719/1000000000000 : ℝ) (73592314857/125000000000 : ℝ) (29436925943/50000000000 : ℝ) (84256047311/200000000000 : ℝ) (105320059141/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 1 (73592314857/125000000000 : ℝ) (29436925943/50000000000 : ℝ) (84256047311/200000000000 : ℝ) (105320059141/250000000000 : ℝ) (101001875541/200000000000 : ℝ) (31563086107/62500000000 : ℝ) (498019982021/1000000000000 : ℝ) (498019982029/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 2 (101001875541/200000000000 : ℝ) (31563086107/62500000000 : ℝ) (498019982021/1000000000000 : ℝ) (498019982029/1000000000000 : ℝ) (501514679863/1000000000000 : ℝ) (501514679871/1000000000000 : ℝ) (501502503687/1000000000000 : ℝ) (31343906481/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 3 (501514679863/1000000000000 : ℝ) (501514679871/1000000000000 : ℝ) (501502503687/1000000000000 : ℝ) (31343906481/62500000000 : ℝ) (20060343671/40000000000 : ℝ) (62688573973/125000000000 : ℝ) (250754295869/500000000000 : ℝ) (501508591747/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 4 (20060343671/40000000000 : ℝ) (62688573973/125000000000 : ℝ) (250754295869/500000000000 : ℝ) (501508591747/1000000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 5 (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 6 (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67119/524288 : ℝ))) 7 (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67119/524288 : ℝ)) hmem 8 (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67119/524288 : ℝ))) hcmem 8 (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67119/524288 : ℝ)) (496023296733/500000000000 : ℝ) (992046593469/1000000000000 : ℝ) (125377147939/250000000000 : ℝ) (250754295883/500000000000 : ℝ) (794083522863/1000000000000 : ℝ) (397041761441/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1046_exp_lower
  have heNumeric : (41098044337/20000000000 : ℝ)/4 ≤ Real.exp (-42628230230073/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098044337/20000000000 : ℝ)/4 ≤ Real.exp ((33559/262144 : ℝ)-(397041761441/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33559/262144 : ℝ) (67119/524288 : ℝ) (397041761441/500000000000 : ℝ) (41098044337/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1047; no trusted numerical premise.
theorem cover8_leaf1047_exp_radius : (124750208431477491/125000000000000000 : ℝ) ≤ Real.exp ((-4195/262144 : ℝ)/8) ∧ Real.exp ((-4195/262144 : ℝ)/8) ≤ (998001667451819929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4195/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1047_exp_lower : (57507092902608563/62500000000000000 : ℝ) ≤ Real.exp ((-17051291999981/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051291999981/25600000000000 : ℝ)/8) ≤ (920113486441737009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051291999981/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1047_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902224239/1000000000000 : ℝ) ≤ 4*Real.exp (67119/524288 : ℝ)*Real.exp (-mu (radius 8 (4195/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902224239/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4195/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1047_exp_radius
  have hrNumeric : (984124707171/1000000000000 : ℝ) ≤ Real.exp (-4195/262144 : ℝ) ∧ Real.exp (-4195/262144 : ℝ) ≤ (246031176793/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984124707171/1000000000000 : ℝ) ≤ (radius 8 (4195/32768 : ℝ)) ∧ (radius 8 (4195/32768 : ℝ)) ≤ (246031176793/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4195/32768 : ℝ)) (984124707171/1000000000000 : ℝ) (246031176793/250000000000 : ℝ) (177478338773/1000000000000 : ℝ) (177478338779/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4195/32768 : ℝ)) (984124707171/1000000000000 : ℝ) (246031176793/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984124707171/1000000000000 : ℝ) (246031176793/250000000000 : ℝ) (198412470717/200000000000 : ℝ) (496031176793/500000000000 : ℝ) (9920305979/10000000000 : ℝ) (496015298951/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 1 (198412470717/200000000000 : ℝ) (496031176793/500000000000 : ℝ) (9920305979/10000000000 : ℝ) (496015298951/500000000000 : ℝ) (496023237871/500000000000 : ℝ) (31001452367/31250000000 : ℝ) (198409295123/200000000000 : ℝ) (992046475617/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 2 (496023237871/500000000000 : ℝ) (31001452367/31250000000 : ℝ) (198409295123/200000000000 : ℝ) (992046475617/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 3 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 4 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 5 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 6 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4195/32768 : ℝ)) 7 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4195/32768 : ℝ))) (177478338773/1000000000000 : ℝ) (177478338779/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177478338773/1000000000000 : ℝ) (177478338779/1000000000000 : ℝ) (294369584693/500000000000 : ℝ) (58873916939/100000000000 : ℝ) (421281780727/1000000000000 : ℝ) (84256356147/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 1 (294369584693/500000000000 : ℝ) (58873916939/100000000000 : ℝ) (421281780727/1000000000000 : ℝ) (84256356147/200000000000 : ℝ) (31563154691/62500000000 : ℝ) (505010475063/1000000000000 : ℝ) (249010584947/500000000000 : ℝ) (498021169901/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 2 (31563154691/62500000000 : ℝ) (505010475063/1000000000000 : ℝ) (249010584947/500000000000 : ℝ) (498021169901/1000000000000 : ℝ) (20060632899/40000000000 : ℝ) (250757911241/500000000000 : ℝ) (250751823321/500000000000 : ℝ) (10030072933/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 3 (20060632899/40000000000 : ℝ) (250757911241/500000000000 : ℝ) (250751823321/500000000000 : ℝ) (10030072933/20000000000 : ℝ) (250754867279/500000000000 : ℝ) (250754867283/500000000000 : ℝ) (501509734521/1000000000000 : ℝ) (50150973453/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 4 (250754867279/500000000000 : ℝ) (250754867283/500000000000 : ℝ) (501509734521/1000000000000 : ℝ) (50150973453/100000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 5 (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 6 (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4195/32768 : ℝ))) 7 (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4195/32768 : ℝ)) hmem 8 (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4195/32768 : ℝ))) hcmem 8 (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4195/32768 : ℝ)) (496023237839/500000000000 : ℝ) (992046475681/1000000000000 : ℝ) (501509734539/1000000000000 : ℝ) (125377433637/250000000000 : ℝ) (794085426617/1000000000000 : ℝ) (158817085327/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1047_exp_lower
  have heNumeric : (2054902224239/1000000000000 : ℝ)/4 ≤ Real.exp (-17051291999981/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902224239/1000000000000 : ℝ)/4 ≤ Real.exp ((67119/524288 : ℝ)-(158817085327/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67119/524288 : ℝ) (4195/32768 : ℝ) (158817085327/200000000000 : ℝ) (2054902224239/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1048; no trusted numerical premise.
theorem cover8_leaf1048_exp_radius : (499000818854526467/500000000000000000 : ℝ) ≤ Real.exp ((-67121/4194304 : ℝ)/8) ∧ Real.exp ((-67121/4194304 : ℝ)/8) ≤ (199600327541810587/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67121/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1048_exp_lower : (920113486858046129/1000000000000000000 : ℝ) ≤ Real.exp ((-5328528721037/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328528721037/8000000000000 : ℝ)/8) ≤ (92011348685804613/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328528721037/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1048_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902231677/1000000000000 : ℝ) ≤ 4*Real.exp (4195/32768 : ℝ)*Real.exp (-mu (radius 8 (67121/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902231677/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67121/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1048_exp_radius
  have hrNumeric : (492062236269/500000000000 : ℝ) ≤ Real.exp (-67121/4194304 : ℝ) ∧ Real.exp (-67121/4194304 : ℝ) ≤ (984124472539/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492062236269/500000000000 : ℝ) ≤ (radius 8 (67121/524288 : ℝ)) ∧ (radius 8 (67121/524288 : ℝ)) ≤ (984124472539/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67121/524288 : ℝ)) (492062236269/500000000000 : ℝ) (984124472539/1000000000000 : ℝ) (177479639817/1000000000000 : ℝ) (11092477489/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67121/524288 : ℝ)) (492062236269/500000000000 : ℝ) (984124472539/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492062236269/500000000000 : ℝ) (984124472539/1000000000000 : ℝ) (992062236269/1000000000000 : ℝ) (99206223627/100000000000 : ℝ) (992030479641/1000000000000 : ℝ) (992030479643/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 1 (992062236269/1000000000000 : ℝ) (99206223627/100000000000 : ℝ) (992030479641/1000000000000 : ℝ) (992030479643/1000000000000 : ℝ) (198409271591/200000000000 : ℝ) (992046357957/1000000000000 : ℝ) (992046357827/1000000000000 : ℝ) (99204635783/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 2 (198409271591/200000000000 : ℝ) (992046357957/1000000000000 : ℝ) (992046357827/1000000000000 : ℝ) (99204635783/100000000000 : ℝ) (992046357891/1000000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 3 (992046357891/1000000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 4 (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 5 (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 6 (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67121/524288 : ℝ)) 7 (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67121/524288 : ℝ))) (177479639817/1000000000000 : ℝ) (11092477489/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177479639817/1000000000000 : ℝ) (11092477489/62500000000 : ℝ) (147184954977/250000000000 : ℝ) (73592477489/125000000000 : ℝ) (210641662437/500000000000 : ℝ) (421283324883/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 1 (147184954977/250000000000 : ℝ) (73592477489/125000000000 : ℝ) (210641662437/500000000000 : ℝ) (421283324883/1000000000000 : ℝ) (505011572391/1000000000000 : ℝ) (252505786199/500000000000 : ℝ) (498022357747/1000000000000 : ℝ) (99604471551/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 2 (505011572391/1000000000000 : ℝ) (252505786199/500000000000 : ℝ) (498022357747/1000000000000 : ℝ) (99604471551/200000000000 : ℝ) (501516965069/1000000000000 : ℝ) (501516965077/1000000000000 : ℝ) (25075239479/50000000000 : ℝ) (125376197397/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 3 (501516965069/1000000000000 : ℝ) (501516965077/1000000000000 : ℝ) (25075239479/50000000000 : ℝ) (125376197397/250000000000 : ℝ) (125377719331/250000000000 : ℝ) (501510877333/1000000000000 : ℝ) (501510877287/1000000000000 : ℝ) (31344429831/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 4 (125377719331/250000000000 : ℝ) (501510877333/1000000000000 : ℝ) (501510877287/1000000000000 : ℝ) (31344429831/62500000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 5 (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 6 (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67121/524288 : ℝ))) 7 (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67121/524288 : ℝ)) hmem 8 (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67121/524288 : ℝ))) hcmem 8 (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67121/524288 : ℝ)) (99204635789/100000000000 : ℝ) (496023178947/500000000000 : ℝ) (100302175461/200000000000 : ℝ) (100302175463/200000000000 : ℝ) (99260916293/125000000000 : ℝ) (198521832591/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1048_exp_lower
  have heNumeric : (2054902231677/1000000000000 : ℝ)/4 ≤ Real.exp (-5328528721037/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902231677/1000000000000 : ℝ)/4 ≤ Real.exp ((4195/32768 : ℝ)-(198521832591/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4195/32768 : ℝ) (67121/524288 : ℝ) (198521832591/250000000000 : ℝ) (2054902231677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1049; no trusted numerical premise.
theorem cover8_leaf1049_exp_radius : (998001607966286827/1000000000000000000 : ℝ) ≤ Real.exp ((-33561/2097152 : ℝ)/8) ∧ Real.exp ((-33561/2097152 : ℝ)/8) ≤ (249500401991571707/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33561/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1049_exp_lower : (184022697455170087/200000000000000000 : ℝ) ≤ Real.exp ((-17051291814323/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051291814323/25600000000000 : ℝ)/8) ≤ (230028371818962609/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051291814323/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1049_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902239141/1000000000000 : ℝ) ≤ 4*Real.exp (67121/524288 : ℝ)*Real.exp (-mu (radius 8 (33561/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902239141/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33561/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1049_exp_radius
  have hrNumeric : (61507764869/62500000000 : ℝ) ≤ Real.exp (-33561/2097152 : ℝ) ∧ Real.exp (-33561/2097152 : ℝ) ≤ (196824847581/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61507764869/62500000000 : ℝ) ≤ (radius 8 (33561/262144 : ℝ)) ∧ (radius 8 (33561/262144 : ℝ)) ≤ (196824847581/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33561/262144 : ℝ)) (61507764869/62500000000 : ℝ) (196824847581/200000000000 : ℝ) (88740470429/500000000000 : ℝ) (2773139701/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33561/262144 : ℝ)) (61507764869/62500000000 : ℝ) (196824847581/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61507764869/62500000000 : ℝ) (196824847581/200000000000 : ℝ) (124007764869/125000000000 : ℝ) (992062118953/1000000000000 : ℝ) (496015180691/500000000000 : ℝ) (992030361383/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 1 (124007764869/125000000000 : ℝ) (992062118953/1000000000000 : ℝ) (496015180691/500000000000 : ℝ) (992030361383/1000000000000 : ℝ) (992046240167/1000000000000 : ℝ) (124005780021/125000000000 : ℝ) (992046240039/1000000000000 : ℝ) (992046240041/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 2 (992046240167/1000000000000 : ℝ) (124005780021/125000000000 : ℝ) (992046240039/1000000000000 : ℝ) (992046240041/1000000000000 : ℝ) (992046240103/1000000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 3 (992046240103/1000000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 4 (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 5 (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 6 (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33561/262144 : ℝ)) 7 (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33561/262144 : ℝ))) (88740470429/500000000000 : ℝ) (2773139701/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88740470429/500000000000 : ℝ) (2773139701/15625000000 : ℝ) (588740470429/1000000000000 : ℝ) (18398139701/31250000000 : ℝ) (421284869011/1000000000000 : ℝ) (421284869019/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 1 (588740470429/1000000000000 : ℝ) (18398139701/31250000000 : ℝ) (421284869011/1000000000000 : ℝ) (421284869019/1000000000000 : ℝ) (12625316743/25000000000 : ℝ) (252506334863/500000000000 : ℝ) (249011772797/500000000000 : ℝ) (498023545601/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 2 (12625316743/25000000000 : ℝ) (252506334863/500000000000 : ℝ) (249011772797/500000000000 : ℝ) (498023545601/1000000000000 : ℝ) (501518107657/1000000000000 : ℝ) (31344881729/62500000000 : ℝ) (501505932511/1000000000000 : ℝ) (250752966259/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 3 (501518107657/1000000000000 : ℝ) (31344881729/62500000000 : ℝ) (501505932511/1000000000000 : ℝ) (250752966259/500000000000 : ℝ) (125378005021/250000000000 : ℝ) (501512020091/1000000000000 : ℝ) (501512020047/1000000000000 : ℝ) (100302404011/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 4 (125378005021/250000000000 : ℝ) (501512020091/1000000000000 : ℝ) (501512020047/1000000000000 : ℝ) (100302404011/200000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 5 (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 6 (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33561/262144 : ℝ))) 7 (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33561/262144 : ℝ)) hmem 8 (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33561/262144 : ℝ))) hcmem 8 (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33561/262144 : ℝ)) (496023120051/500000000000 : ℝ) (198409248021/200000000000 : ℝ) (100302404013/200000000000 : ℝ) (501512020073/1000000000000 : ℝ) (49630577129/62500000000 : ℝ) (4963057713/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1049_exp_lower
  have heNumeric : (2054902239141/1000000000000 : ℝ)/4 ≤ Real.exp (-17051291814323/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902239141/1000000000000 : ℝ)/4 ≤ Real.exp ((67121/524288 : ℝ)-(4963057713/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67121/524288 : ℝ) (33561/262144 : ℝ) (4963057713/6250000000 : ℝ) (2054902239141/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1025_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1025_certificate
#check SmaleRate.Proofs.cover8_leaf1026_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1026_certificate
#check SmaleRate.Proofs.cover8_leaf1027_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1027_certificate
#check SmaleRate.Proofs.cover8_leaf1028_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1028_certificate
#check SmaleRate.Proofs.cover8_leaf1029_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1029_certificate
#check SmaleRate.Proofs.cover8_leaf1030_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1030_certificate
#check SmaleRate.Proofs.cover8_leaf1031_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1031_certificate
#check SmaleRate.Proofs.cover8_leaf1032_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1032_certificate
#check SmaleRate.Proofs.cover8_leaf1033_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1033_certificate
#check SmaleRate.Proofs.cover8_leaf1034_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1034_certificate
#check SmaleRate.Proofs.cover8_leaf1035_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1035_certificate
#check SmaleRate.Proofs.cover8_leaf1036_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1036_certificate
#check SmaleRate.Proofs.cover8_leaf1037_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1037_certificate
#check SmaleRate.Proofs.cover8_leaf1038_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1038_certificate
#check SmaleRate.Proofs.cover8_leaf1039_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1039_certificate
#check SmaleRate.Proofs.cover8_leaf1040_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1040_certificate
#check SmaleRate.Proofs.cover8_leaf1041_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1041_certificate
#check SmaleRate.Proofs.cover8_leaf1042_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1042_certificate
#check SmaleRate.Proofs.cover8_leaf1043_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1043_certificate
#check SmaleRate.Proofs.cover8_leaf1044_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1044_certificate
#check SmaleRate.Proofs.cover8_leaf1045_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1045_certificate
#check SmaleRate.Proofs.cover8_leaf1046_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1046_certificate
#check SmaleRate.Proofs.cover8_leaf1047_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1047_certificate
#check SmaleRate.Proofs.cover8_leaf1048_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1048_certificate
#check SmaleRate.Proofs.cover8_leaf1049_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1049_certificate
