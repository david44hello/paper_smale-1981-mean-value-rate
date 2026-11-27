/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0600; no trusted numerical premise.
theorem cover8_leaf0600_exp_radius : (998014962557420299/1000000000000000000 : ℝ) ≤ Real.exp ((-66673/4194304 : ℝ)/8) ∧ Real.exp ((-66673/4194304 : ℝ)/8) ≤ (9980149625574203/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66673/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0600_exp_lower : (920113522918962091/1000000000000000000 : ℝ) ≤ Real.exp ((-5328526212761/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328526212761/8000000000000 : ℝ)/8) ≤ (230028380729740523/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328526212761/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0600_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372571899/25000000000 : ℝ) ≤ 4*Real.exp (4167/32768 : ℝ)*Real.exp (-mu (radius 8 (66673/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (51372571899/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66673/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0600_exp_radius
  have hrNumeric : (492114796993/500000000000 : ℝ) ≤ Real.exp (-66673/4194304 : ℝ) ∧ Real.exp (-66673/4194304 : ℝ) ≤ (984229593987/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492114796993/500000000000 : ℝ) ≤ (radius 8 (66673/524288 : ℝ)) ∧ (radius 8 (66673/524288 : ℝ)) ≤ (984229593987/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66673/524288 : ℝ)) (492114796993/500000000000 : ℝ) (984229593987/1000000000000 : ℝ) (22111968733/125000000000 : ℝ) (176895749871/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66673/524288 : ℝ)) (492114796993/500000000000 : ℝ) (984229593987/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492114796993/500000000000 : ℝ) (984229593987/1000000000000 : ℝ) (992114796993/1000000000000 : ℝ) (496057398497/500000000000 : ℝ) (992083461199/1000000000000 : ℝ) (992083461201/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 1 (992114796993/1000000000000 : ℝ) (496057398497/500000000000 : ℝ) (992083461199/1000000000000 : ℝ) (992083461201/1000000000000 : ℝ) (124012391137/125000000000 : ℝ) (496049564549/500000000000 : ℝ) (248024782243/250000000000 : ℝ) (496049564487/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 2 (124012391137/125000000000 : ℝ) (496049564549/500000000000 : ℝ) (248024782243/250000000000 : ℝ) (496049564487/500000000000 : ℝ) (496049564517/500000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 3 (496049564517/500000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 4 (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 5 (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 6 (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66673/524288 : ℝ)) 7 (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66673/524288 : ℝ))) (22111968733/125000000000 : ℝ) (176895749871/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22111968733/125000000000 : ℝ) (176895749871/1000000000000 : ℝ) (147111968733/250000000000 : ℝ) (73555984367/125000000000 : ℝ) (84117952867/200000000000 : ℝ) (84117952869/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 1 (147111968733/250000000000 : ℝ) (73555984367/125000000000 : ℝ) (84117952867/200000000000 : ℝ) (84117952869/200000000000 : ℝ) (504518819633/1000000000000 : ℝ) (504518819641/1000000000000 : ℝ) (31093052947/62500000000 : ℝ) (497488847161/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 2 (504518819633/1000000000000 : ℝ) (504518819641/1000000000000 : ℝ) (31093052947/62500000000 : ℝ) (497488847161/1000000000000 : ℝ) (31312739587/62500000000 : ℝ) (501003833401/1000000000000 : ℝ) (500991502867/1000000000000 : ℝ) (500991502877/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 3 (31312739587/62500000000 : ℝ) (501003833401/1000000000000 : ℝ) (500991502867/1000000000000 : ℝ) (500991502877/1000000000000 : ℝ) (500997668129/1000000000000 : ℝ) (500997668139/1000000000000 : ℝ) (500997668091/1000000000000 : ℝ) (250498834051/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 4 (500997668129/1000000000000 : ℝ) (500997668139/1000000000000 : ℝ) (500997668091/1000000000000 : ℝ) (250498834051/500000000000 : ℝ) (50099766811/100000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 5 (50099766811/100000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 6 (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66673/524288 : ℝ))) 7 (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66673/524288 : ℝ)) hmem 8 (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66673/524288 : ℝ))) hcmem 8 (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66673/524288 : ℝ)) (992099129033/1000000000000 : ℝ) (248024782259/250000000000 : ℝ) (500997668109/1000000000000 : ℝ) (500997668121/1000000000000 : ℝ) (793232524619/1000000000000 : ℝ) (396616262321/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0600_exp_lower
  have heNumeric : (51372571899/25000000000 : ℝ)/4 ≤ Real.exp (-5328526212761/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372571899/25000000000 : ℝ)/4 ≤ Real.exp ((4167/32768 : ℝ)-(396616262321/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4167/32768 : ℝ) (66673/524288 : ℝ) (396616262321/500000000000 : ℝ) (51372571899/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0601; no trusted numerical premise.
theorem cover8_leaf0601_exp_radius : (24950373320356427/25000000000000000 : ℝ) ≤ Real.exp ((-33337/2097152 : ℝ)/8) ∧ Real.exp ((-33337/2097152 : ℝ)/8) ≤ (998014932814257081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33337/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0601_exp_lower : (36804540893597537/40000000000000000 : ℝ) ≤ Real.exp ((-3410256801943/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410256801943/5120000000000 : ℝ)/8) ≤ (460056761169969213/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410256801943/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0601_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451432807/500000000000 : ℝ) ≤ 4*Real.exp (66673/524288 : ℝ)*Real.exp (-mu (radius 8 (33337/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451432807/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33337/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0601_exp_radius
  have hrNumeric : (984229359327/1000000000000 : ℝ) ≤ Real.exp (-33337/2097152 : ℝ) ∧ Real.exp (-33337/2097152 : ℝ) ≤ (30757167479/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984229359327/1000000000000 : ℝ) ≤ (radius 8 (33337/262144 : ℝ)) ∧ (radius 8 (33337/262144 : ℝ)) ≤ (30757167479/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33337/262144 : ℝ)) (984229359327/1000000000000 : ℝ) (30757167479/31250000000 : ℝ) (88448527739/500000000000 : ℝ) (44224263871/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33337/262144 : ℝ)) (984229359327/1000000000000 : ℝ) (30757167479/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984229359327/1000000000000 : ℝ) (30757167479/31250000000 : ℝ) (992114679663/1000000000000 : ℝ) (62007167479/62500000000 : ℝ) (992083342933/1000000000000 : ℝ) (198416668587/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 1 (992114679663/1000000000000 : ℝ) (62007167479/62500000000 : ℝ) (992083342933/1000000000000 : ℝ) (198416668587/200000000000 : ℝ) (496049505649/500000000000 : ℝ) (9920990113/10000000000 : ℝ) (496049505587/500000000000 : ℝ) (124012376397/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 2 (496049505649/500000000000 : ℝ) (9920990113/10000000000 : ℝ) (496049505587/500000000000 : ℝ) (124012376397/125000000000 : ℝ) (248024752809/250000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 3 (248024752809/250000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 4 (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 5 (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 6 (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33337/262144 : ℝ)) 7 (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33337/262144 : ℝ))) (88448527739/500000000000 : ℝ) (44224263871/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88448527739/500000000000 : ℝ) (44224263871/250000000000 : ℝ) (588448527739/1000000000000 : ℝ) (294224263871/500000000000 : ℝ) (84118263291/200000000000 : ℝ) (420591316463/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 1 (588448527739/1000000000000 : ℝ) (294224263871/500000000000 : ℝ) (84118263291/200000000000 : ℝ) (420591316463/1000000000000 : ℝ) (504519922097/1000000000000 : ℝ) (504519922103/1000000000000 : ℝ) (497490041053/1000000000000 : ℝ) (24874502053/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 2 (504519922097/1000000000000 : ℝ) (504519922103/1000000000000 : ℝ) (497490041053/1000000000000 : ℝ) (24874502053/50000000000 : ℝ) (20040199263/40000000000 : ℝ) (250502490791/500000000000 : ℝ) (500992651399/1000000000000 : ℝ) (250496325703/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 3 (20040199263/40000000000 : ℝ) (250502490791/500000000000 : ℝ) (500992651399/1000000000000 : ℝ) (250496325703/500000000000 : ℝ) (500998816487/1000000000000 : ℝ) (250499408247/500000000000 : ℝ) (500998816449/1000000000000 : ℝ) (500998816457/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 4 (500998816487/1000000000000 : ℝ) (250499408247/500000000000 : ℝ) (500998816449/1000000000000 : ℝ) (500998816457/1000000000000 : ℝ) (125249704117/250000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 5 (125249704117/250000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 6 (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33337/262144 : ℝ))) 7 (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33337/262144 : ℝ)) hmem 8 (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33337/262144 : ℝ))) hcmem 8 (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33337/262144 : ℝ)) (198419802247/200000000000 : ℝ) (496049505619/500000000000 : ℝ) (500998816467/1000000000000 : ℝ) (125249704119/250000000000 : ℝ) (793234437007/1000000000000 : ℝ) (31729377481/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0601_exp_lower
  have heNumeric : (1027451432807/500000000000 : ℝ)/4 ≤ Real.exp (-3410256801943/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451432807/500000000000 : ℝ)/4 ≤ Real.exp ((66673/524288 : ℝ)-(31729377481/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66673/524288 : ℝ) (33337/262144 : ℝ) (31729377481/40000000000 : ℝ) (1027451432807/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0602; no trusted numerical premise.
theorem cover8_leaf0602_exp_radius : (249503725767773687/250000000000000000 : ℝ) ≤ Real.exp ((-66675/4194304 : ℝ)/8) ∧ Real.exp ((-66675/4194304 : ℝ)/8) ≤ (998014903071094749/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66675/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0602_exp_lower : (920113521763905129/1000000000000000000 : ℝ) ≤ Real.exp ((-42628210344823/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628210344823/64000000000000 : ℝ)/8) ≤ (92011352176390513/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628210344823/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0602_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902855323/1000000000000 : ℝ) ≤ 4*Real.exp (33337/262144 : ℝ)*Real.exp (-mu (radius 8 (66675/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902855323/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66675/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0602_exp_radius
  have hrNumeric : (984229124669/1000000000000 : ℝ) ≤ Real.exp (-66675/4194304 : ℝ) ∧ Real.exp (-66675/4194304 : ℝ) ≤ (98422912467/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984229124669/1000000000000 : ℝ) ≤ (radius 8 (66675/524288 : ℝ)) ∧ (radius 8 (66675/524288 : ℝ)) ≤ (98422912467/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66675/524288 : ℝ)) (984229124669/1000000000000 : ℝ) (98422912467/100000000000 : ℝ) (7075934443/40000000000 : ℝ) (88449180541/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66675/524288 : ℝ)) (984229124669/1000000000000 : ℝ) (98422912467/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984229124669/1000000000000 : ℝ) (98422912467/100000000000 : ℝ) (496057281167/500000000000 : ℝ) (198422912467/200000000000 : ℝ) (248020806167/250000000000 : ℝ) (99208322467/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 1 (496057281167/500000000000 : ℝ) (198422912467/200000000000 : ℝ) (248020806167/250000000000 : ℝ) (99208322467/100000000000 : ℝ) (992098893501/1000000000000 : ℝ) (992098893503/1000000000000 : ℝ) (992098893377/1000000000000 : ℝ) (992098893379/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 2 (992098893501/1000000000000 : ℝ) (992098893503/1000000000000 : ℝ) (992098893377/1000000000000 : ℝ) (992098893379/1000000000000 : ℝ) (992098893439/1000000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 3 (992098893439/1000000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 4 (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 5 (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 6 (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66675/524288 : ℝ)) 7 (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66675/524288 : ℝ))) (7075934443/40000000000 : ℝ) (88449180541/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7075934443/40000000000 : ℝ) (88449180541/500000000000 : ℝ) (588449180537/1000000000000 : ℝ) (588449180541/1000000000000 : ℝ) (420592868549/1000000000000 : ℝ) (420592868559/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 1 (588449180537/1000000000000 : ℝ) (588449180541/1000000000000 : ℝ) (420592868549/1000000000000 : ℝ) (420592868559/1000000000000 : ℝ) (504521024543/1000000000000 : ℝ) (10090420491/20000000000 : ℝ) (99498246987/200000000000 : ℝ) (497491234943/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 2 (504521024543/1000000000000 : ℝ) (10090420491/20000000000 : ℝ) (99498246987/200000000000 : ℝ) (497491234943/1000000000000 : ℝ) (501006129739/1000000000000 : ℝ) (501006129747/1000000000000 : ℝ) (62624224989/125000000000 : ℝ) (6262422499/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 3 (501006129739/1000000000000 : ℝ) (501006129747/1000000000000 : ℝ) (62624224989/125000000000 : ℝ) (6262422499/12500000000 : ℝ) (20039998593/40000000000 : ℝ) (250499982417/500000000000 : ℝ) (500999964787/1000000000000 : ℝ) (125249991199/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 4 (20039998593/40000000000 : ℝ) (250499982417/500000000000 : ℝ) (500999964787/1000000000000 : ℝ) (125249991199/250000000000 : ℝ) (250499982403/500000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 5 (250499982403/500000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 6 (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66675/524288 : ℝ))) 7 (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66675/524288 : ℝ)) hmem 8 (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66675/524288 : ℝ))) hcmem 8 (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66675/524288 : ℝ)) (496049446719/500000000000 : ℝ) (992098893441/1000000000000 : ℝ) (100199992961/200000000000 : ℝ) (100199992963/200000000000 : ℝ) (396618174681/500000000000 : ℝ) (396618174691/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0602_exp_lower
  have heNumeric : (2054902855323/1000000000000 : ℝ)/4 ≤ Real.exp (-42628210344823/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902855323/1000000000000 : ℝ)/4 ≤ Real.exp ((33337/262144 : ℝ)-(396618174691/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33337/262144 : ℝ) (66675/524288 : ℝ) (396618174691/500000000000 : ℝ) (2054902855323/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0603; no trusted numerical premise.
theorem cover8_leaf0603_exp_radius : (499007436663966651/500000000000000000 : ℝ) ≤ Real.exp ((-16669/1048576 : ℝ)/8) ∧ Real.exp ((-16669/1048576 : ℝ)/8) ≤ (998014873327933303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16669/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0603_exp_lower : (36804540847560879/40000000000000000 : ℝ) ≤ Real.exp ((-85256421329437/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256421329437/128000000000000 : ℝ)/8) ≤ (115014190148627747/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256421329437/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0603_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725711263/250000000000 : ℝ) ≤ 4*Real.exp (66675/524288 : ℝ)*Real.exp (-mu (radius 8 (16669/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725711263/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16669/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0603_exp_radius
  have hrNumeric : (98422889001/100000000000 : ℝ) ≤ Real.exp (-16669/1048576 : ℝ) ∧ Real.exp (-16669/1048576 : ℝ) ≤ (984228890011/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98422889001/100000000000 : ℝ) ≤ (radius 8 (16669/131072 : ℝ)) ∧ (radius 8 (16669/131072 : ℝ)) ≤ (984228890011/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16669/131072 : ℝ)) (98422889001/100000000000 : ℝ) (984228890011/1000000000000 : ℝ) (176899666669/1000000000000 : ℝ) (7075986667/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16669/131072 : ℝ)) (98422889001/100000000000 : ℝ) (984228890011/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98422889001/100000000000 : ℝ) (984228890011/1000000000000 : ℝ) (198422889001/200000000000 : ℝ) (496057222503/500000000000 : ℝ) (496041553201/500000000000 : ℝ) (248020776601/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 1 (198422889001/200000000000 : ℝ) (496057222503/500000000000 : ℝ) (496041553201/500000000000 : ℝ) (248020776601/250000000000 : ℝ) (992098775703/1000000000000 : ℝ) (198419755141/200000000000 : ℝ) (992098775579/1000000000000 : ℝ) (496049387791/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 2 (992098775703/1000000000000 : ℝ) (198419755141/200000000000 : ℝ) (992098775579/1000000000000 : ℝ) (496049387791/500000000000 : ℝ) (992098775641/1000000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 3 (992098775641/1000000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 4 (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 5 (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 6 (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16669/131072 : ℝ)) 7 (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16669/131072 : ℝ))) (176899666669/1000000000000 : ℝ) (7075986667/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176899666669/1000000000000 : ℝ) (7075986667/40000000000 : ℝ) (294224916667/500000000000 : ℝ) (294224916669/500000000000 : ℝ) (210297210317/500000000000 : ℝ) (210297210321/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 1 (294224916667/500000000000 : ℝ) (294224916669/500000000000 : ℝ) (210297210317/500000000000 : ℝ) (210297210321/500000000000 : ℝ) (63065265873/125000000000 : ℝ) (50452212699/100000000000 : ℝ) (49749242881/100000000000 : ℝ) (497492428817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 2 (63065265873/125000000000 : ℝ) (50452212699/100000000000 : ℝ) (49749242881/100000000000 : ℝ) (497492428817/1000000000000 : ℝ) (501007277897/1000000000000 : ℝ) (31312954869/62500000000 : ℝ) (500994948419/1000000000000 : ℝ) (250497474213/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 3 (501007277897/1000000000000 : ℝ) (31312954869/62500000000 : ℝ) (500994948419/1000000000000 : ℝ) (250497474213/500000000000 : ℝ) (250500556579/500000000000 : ℝ) (100200222633/200000000000 : ℝ) (3131256957/6250000000 : ℝ) (62625139141/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 4 (250500556579/500000000000 : ℝ) (100200222633/200000000000 : ℝ) (3131256957/6250000000 : ℝ) (62625139141/125000000000 : ℝ) (501001113139/1000000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 5 (501001113139/1000000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 6 (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16669/131072 : ℝ))) 7 (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16669/131072 : ℝ)) hmem 8 (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16669/131072 : ℝ))) hcmem 8 (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16669/131072 : ℝ)) (24802469391/25000000000 : ℝ) (248024693911/250000000000 : ℝ) (250500556569/500000000000 : ℝ) (501001113147/1000000000000 : ℝ) (79323826171/100000000000 : ℝ) (793238261729/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0603_exp_lower
  have heNumeric : (513725711263/250000000000 : ℝ)/4 ≤ Real.exp (-85256421329437/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725711263/250000000000 : ℝ)/4 ≤ Real.exp ((66675/524288 : ℝ)-(793238261729/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66675/524288 : ℝ) (16669/131072 : ℝ) (793238261729/1000000000000 : ℝ) (513725711263/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0604; no trusted numerical premise.
theorem cover8_leaf0604_exp_radius : (998014843584772743/1000000000000000000 : ℝ) ≤ Real.exp ((-66677/4194304 : ℝ)/8) ∧ Real.exp ((-66677/4194304 : ℝ)/8) ≤ (124751855448096593/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66677/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0604_exp_lower : (230028380154311051/250000000000000000 : ℝ) ≤ Real.exp ((-21314105491443/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314105491443/32000000000000 : ℝ)/8) ≤ (184022704123448841/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314105491443/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0604_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725708709/250000000000 : ℝ) ≤ 4*Real.exp (16669/131072 : ℝ)*Real.exp (-mu (radius 8 (66677/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725708709/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66677/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0604_exp_radius
  have hrNumeric : (123028581919/125000000000 : ℝ) ≤ Real.exp (-66677/4194304 : ℝ) ∧ Real.exp (-66677/4194304 : ℝ) ≤ (984228655353/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123028581919/125000000000 : ℝ) ≤ (radius 8 (66677/524288 : ℝ)) ∧ (radius 8 (66677/524288 : ℝ)) ≤ (984228655353/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66677/524288 : ℝ)) (123028581919/125000000000 : ℝ) (984228655353/1000000000000 : ℝ) (176900972247/1000000000000 : ℝ) (176900972253/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66677/524288 : ℝ)) (123028581919/125000000000 : ℝ) (984228655353/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123028581919/125000000000 : ℝ) (984228655353/1000000000000 : ℝ) (248028581919/250000000000 : ℝ) (992114327677/1000000000000 : ℝ) (992082988137/1000000000000 : ℝ) (992082988139/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 1 (248028581919/250000000000 : ℝ) (992114327677/1000000000000 : ℝ) (992082988137/1000000000000 : ℝ) (992082988139/1000000000000 : ℝ) (496049328953/500000000000 : ℝ) (248024664477/250000000000 : ℝ) (496049328891/500000000000 : ℝ) (198419731557/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 2 (496049328953/500000000000 : ℝ) (248024664477/250000000000 : ℝ) (496049328891/500000000000 : ℝ) (198419731557/200000000000 : ℝ) (248024664461/250000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 3 (248024664461/250000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 4 (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 5 (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 6 (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66677/524288 : ℝ)) 7 (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66677/524288 : ℝ))) (176900972247/1000000000000 : ℝ) (176900972253/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176900972247/1000000000000 : ℝ) (176900972253/1000000000000 : ℝ) (588450486123/1000000000000 : ℝ) (588450486127/1000000000000 : ℝ) (210297986347/500000000000 : ℝ) (210297986351/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 1 (588450486123/1000000000000 : ℝ) (588450486127/1000000000000 : ℝ) (210297986347/500000000000 : ℝ) (210297986351/500000000000 : ℝ) (15766350919/31250000000 : ℝ) (100904645883/200000000000 : ℝ) (99498724533/200000000000 : ℝ) (497493622673/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 2 (15766350919/31250000000 : ℝ) (100904645883/200000000000 : ℝ) (99498724533/200000000000 : ℝ) (497493622673/1000000000000 : ℝ) (125252106509/250000000000 : ℝ) (125252106511/250000000000 : ℝ) (500996096907/1000000000000 : ℝ) (125249024229/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 3 (125252106509/250000000000 : ℝ) (125252106511/250000000000 : ℝ) (500996096907/1000000000000 : ℝ) (125249024229/250000000000 : ℝ) (501002261471/1000000000000 : ℝ) (12525056537/25000000000 : ℝ) (501002261433/1000000000000 : ℝ) (501002261443/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 4 (501002261471/1000000000000 : ℝ) (12525056537/25000000000 : ℝ) (501002261433/1000000000000 : ℝ) (501002261443/1000000000000 : ℝ) (125250565363/250000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 5 (125250565363/250000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 6 (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66677/524288 : ℝ))) 7 (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66677/524288 : ℝ)) hmem 8 (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66677/524288 : ℝ))) hcmem 8 (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66677/524288 : ℝ)) (992098657843/1000000000000 : ℝ) (992098657847/1000000000000 : ℝ) (501002261451/1000000000000 : ℝ) (250501130731/500000000000 : ℝ) (793240174027/1000000000000 : ℝ) (793240174049/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0604_exp_lower
  have heNumeric : (513725708709/250000000000 : ℝ)/4 ≤ Real.exp (-21314105491443/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725708709/250000000000 : ℝ)/4 ≤ Real.exp ((16669/131072 : ℝ)-(793240174049/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16669/131072 : ℝ) (66677/524288 : ℝ) (793240174049/1000000000000 : ℝ) (513725708709/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0605; no trusted numerical premise.
theorem cover8_leaf0605_exp_radius : (99801481384161307/100000000000000000 : ℝ) ≤ Real.exp ((-33339/2097152 : ℝ)/8) ∧ Real.exp ((-33339/2097152 : ℝ)/8) ≤ (998014813841613071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33339/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0605_exp_lower : (920113520047766717/1000000000000000000 : ℝ) ≤ Real.exp ((-85256422599547/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256422599547/128000000000000 : ℝ)/8) ≤ (460056760023883359/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256422599547/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0605_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902824661/1000000000000 : ℝ) ≤ 4*Real.exp (66677/524288 : ℝ)*Real.exp (-mu (radius 8 (33339/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902824661/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33339/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0605_exp_radius
  have hrNumeric : (492114210347/500000000000 : ℝ) ≤ Real.exp (-33339/2097152 : ℝ) ∧ Real.exp (-33339/2097152 : ℝ) ≤ (196845684139/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492114210347/500000000000 : ℝ) ≤ (radius 8 (33339/262144 : ℝ)) ∧ (radius 8 (33339/262144 : ℝ)) ≤ (196845684139/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33339/262144 : ℝ)) (492114210347/500000000000 : ℝ) (196845684139/200000000000 : ℝ) (35380455563/200000000000 : ℝ) (176902277821/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33339/262144 : ℝ)) (492114210347/500000000000 : ℝ) (196845684139/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492114210347/500000000000 : ℝ) (196845684139/200000000000 : ℝ) (992114210347/1000000000000 : ℝ) (248028552587/250000000000 : ℝ) (62005179367/62500000000 : ℝ) (992082869873/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 1 (992114210347/1000000000000 : ℝ) (248028552587/250000000000 : ℝ) (62005179367/62500000000 : ℝ) (992082869873/1000000000000 : ℝ) (992098540109/1000000000000 : ℝ) (992098540111/1000000000000 : ℝ) (198419707997/200000000000 : ℝ) (992098539987/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 2 (992098540109/1000000000000 : ℝ) (992098540111/1000000000000 : ℝ) (198419707997/200000000000 : ℝ) (992098539987/1000000000000 : ℝ) (992098540047/1000000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 3 (992098540047/1000000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 4 (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 5 (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 6 (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33339/262144 : ℝ)) 7 (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33339/262144 : ℝ))) (35380455563/200000000000 : ℝ) (176902277821/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35380455563/200000000000 : ℝ) (176902277821/1000000000000 : ℝ) (588451138907/1000000000000 : ℝ) (588451138911/1000000000000 : ℝ) (420597524737/1000000000000 : ℝ) (84119504949/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 1 (588451138907/1000000000000 : ℝ) (588451138911/1000000000000 : ℝ) (420597524737/1000000000000 : ℝ) (84119504949/200000000000 : ℝ) (252262165911/500000000000 : ℝ) (126131082957/250000000000 : ℝ) (124373704127/250000000000 : ℝ) (124373704129/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 2 (252262165911/500000000000 : ℝ) (126131082957/250000000000 : ℝ) (124373704127/250000000000 : ℝ) (124373704129/250000000000 : ℝ) (100201914833/200000000000 : ℝ) (125252393543/250000000000 : ℝ) (100199449077/200000000000 : ℝ) (500997245393/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 3 (100201914833/200000000000 : ℝ) (125252393543/250000000000 : ℝ) (100199449077/200000000000 : ℝ) (500997245393/1000000000000 : ℝ) (20040136391/40000000000 : ℝ) (501003409783/1000000000000 : ℝ) (501003409737/1000000000000 : ℝ) (100200681949/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 4 (20040136391/40000000000 : ℝ) (501003409783/1000000000000 : ℝ) (501003409737/1000000000000 : ℝ) (100200681949/200000000000 : ℝ) (125250852439/250000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 5 (125250852439/250000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 6 (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33339/262144 : ℝ))) 7 (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33339/262144 : ℝ)) hmem 8 (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33339/262144 : ℝ))) hcmem 8 (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33339/262144 : ℝ)) (496049270023/500000000000 : ℝ) (992098540049/1000000000000 : ℝ) (100200681951/200000000000 : ℝ) (125250852441/250000000000 : ℝ) (793242086331/1000000000000 : ℝ) (793242086349/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0605_exp_lower
  have heNumeric : (2054902824661/1000000000000 : ℝ)/4 ≤ Real.exp (-85256422599547/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902824661/1000000000000 : ℝ)/4 ≤ Real.exp ((66677/524288 : ℝ)-(793242086349/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66677/524288 : ℝ) (33339/262144 : ℝ) (793242086349/1000000000000 : ℝ) (2054902824661/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0606; no trusted numerical premise.
theorem cover8_leaf0606_exp_radius : (998014784098454283/1000000000000000000 : ℝ) ≤ Real.exp ((-66679/4194304 : ℝ)/8) ∧ Real.exp ((-66679/4194304 : ℝ)/8) ≤ (249503696024613571/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66679/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0606_exp_lower : (920113519479439373/1000000000000000000 : ℝ) ≤ Real.exp ((-42628211616021/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628211616021/64000000000000 : ℝ)/8) ≤ (460056759739719687/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628211616021/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0606_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902814507/1000000000000 : ℝ) ≤ 4*Real.exp (33339/262144 : ℝ)*Real.exp (-mu (radius 8 (66679/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902814507/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66679/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0606_exp_radius
  have hrNumeric : (196845637207/200000000000 : ℝ) ≤ Real.exp (-66679/4194304 : ℝ) ∧ Real.exp (-66679/4194304 : ℝ) ≤ (246057046509/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196845637207/200000000000 : ℝ) ≤ (radius 8 (66679/524288 : ℝ)) ∧ (radius 8 (66679/524288 : ℝ)) ≤ (246057046509/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66679/524288 : ℝ)) (196845637207/200000000000 : ℝ) (246057046509/250000000000 : ℝ) (88451791689/500000000000 : ℝ) (35380716677/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66679/524288 : ℝ)) (196845637207/200000000000 : ℝ) (246057046509/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196845637207/200000000000 : ℝ) (246057046509/250000000000 : ℝ) (992114093017/1000000000000 : ℝ) (496057046509/500000000000 : ℝ) (496041375803/500000000000 : ℝ) (992082751607/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 1 (992114093017/1000000000000 : ℝ) (496057046509/500000000000 : ℝ) (496041375803/500000000000 : ℝ) (992082751607/1000000000000 : ℝ) (992098422311/1000000000000 : ℝ) (992098422313/1000000000000 : ℝ) (992098422187/1000000000000 : ℝ) (992098422189/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 2 (992098422311/1000000000000 : ℝ) (992098422313/1000000000000 : ℝ) (992098422187/1000000000000 : ℝ) (992098422189/1000000000000 : ℝ) (992098422249/1000000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 3 (992098422249/1000000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 4 (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 5 (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 6 (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66679/524288 : ℝ)) 7 (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66679/524288 : ℝ))) (88451791689/500000000000 : ℝ) (35380716677/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88451791689/500000000000 : ℝ) (35380716677/200000000000 : ℝ) (588451791689/1000000000000 : ℝ) (588451791693/1000000000000 : ℝ) (420599076767/1000000000000 : ℝ) (420599076777/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 1 (588451791689/1000000000000 : ℝ) (588451791693/1000000000000 : ℝ) (420599076767/1000000000000 : ℝ) (420599076777/1000000000000 : ℝ) (126131358557/250000000000 : ℝ) (100905086847/200000000000 : ℝ) (248748005171/500000000000 : ℝ) (9949920207/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 2 (126131358557/250000000000 : ℝ) (100905086847/200000000000 : ℝ) (248748005171/500000000000 : ℝ) (9949920207/20000000000 : ℝ) (100202144457/200000000000 : ℝ) (501010722293/1000000000000 : ℝ) (250499196927/500000000000 : ℝ) (250499196931/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 3 (100202144457/200000000000 : ℝ) (501010722293/1000000000000 : ℝ) (250499196927/500000000000 : ℝ) (250499196931/500000000000 : ℝ) (501004558069/1000000000000 : ℝ) (250502279039/500000000000 : ℝ) (501004558031/1000000000000 : ℝ) (12525113951/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 4 (501004558069/1000000000000 : ℝ) (250502279039/500000000000 : ℝ) (501004558031/1000000000000 : ℝ) (12525113951/25000000000 : ℝ) (10020091161/20000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 5 (10020091161/20000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 6 (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66679/524288 : ℝ))) 7 (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66679/524288 : ℝ)) hmem 8 (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66679/524288 : ℝ))) hcmem 8 (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66679/524288 : ℝ)) (124012302781/125000000000 : ℝ) (992098422251/1000000000000 : ℝ) (501004558049/1000000000000 : ℝ) (501004558059/1000000000000 : ℝ) (793243998619/1000000000000 : ℝ) (793243998639/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0606_exp_lower
  have heNumeric : (2054902814507/1000000000000 : ℝ)/4 ≤ Real.exp (-42628211616021/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902814507/1000000000000 : ℝ)/4 ≤ Real.exp ((33339/262144 : ℝ)-(793243998639/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33339/262144 : ℝ) (66679/524288 : ℝ) (793243998639/1000000000000 : ℝ) (2054902814507/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0607; no trusted numerical premise.
theorem cover8_leaf0607_exp_radius : (998014754355296383/1000000000000000000 : ℝ) ≤ Real.exp ((-8335/524288 : ℝ)/8) ∧ Real.exp ((-8335/524288 : ℝ)/8) ≤ (7796990268400753/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-8335/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0607_exp_lower : (460056759457166213/500000000000000000 : ℝ) ≤ Real.exp ((-85256423860953/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256423860953/128000000000000 : ℝ)/8) ≤ (920113518914332427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256423860953/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0607_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902804411/1000000000000 : ℝ) ≤ 4*Real.exp (66679/524288 : ℝ)*Real.exp (-mu (radius 8 (8335/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902804411/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8335/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0607_exp_radius
  have hrNumeric : (984227951377/1000000000000 : ℝ) ≤ Real.exp (-8335/524288 : ℝ) ∧ Real.exp (-8335/524288 : ℝ) ≤ (492113975689/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984227951377/1000000000000 : ℝ) ≤ (radius 8 (8335/65536 : ℝ)) ∧ (radius 8 (8335/65536 : ℝ)) ≤ (492113975689/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8335/65536 : ℝ)) (984227951377/1000000000000 : ℝ) (492113975689/500000000000 : ℝ) (88452444463/500000000000 : ℝ) (176904888933/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8335/65536 : ℝ)) (984227951377/1000000000000 : ℝ) (492113975689/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984227951377/1000000000000 : ℝ) (492113975689/500000000000 : ℝ) (124014246961/125000000000 : ℝ) (992113975689/1000000000000 : ℝ) (992082633341/1000000000000 : ℝ) (496041316671/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 1 (124014246961/125000000000 : ℝ) (992113975689/1000000000000 : ℝ) (992082633341/1000000000000 : ℝ) (496041316671/500000000000 : ℝ) (496049152257/500000000000 : ℝ) (248024576129/250000000000 : ℝ) (99209830439/100000000000 : ℝ) (124012288049/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 2 (496049152257/500000000000 : ℝ) (248024576129/250000000000 : ℝ) (99209830439/100000000000 : ℝ) (124012288049/125000000000 : ℝ) (248024576113/250000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 3 (248024576113/250000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 4 (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 5 (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 6 (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8335/65536 : ℝ)) 7 (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8335/65536 : ℝ))) (88452444463/500000000000 : ℝ) (176904888933/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88452444463/500000000000 : ℝ) (176904888933/1000000000000 : ℝ) (588452444463/1000000000000 : ℝ) (588452444467/1000000000000 : ℝ) (16824025151/40000000000 : ℝ) (26287539299/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 1 (588452444463/1000000000000 : ℝ) (588452444467/1000000000000 : ℝ) (16824025151/40000000000 : ℝ) (26287539299/62500000000 : ℝ) (504526536619/1000000000000 : ℝ) (252263268313/500000000000 : ℝ) (248748602079/500000000000 : ℝ) (248748602083/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 2 (504526536619/1000000000000 : ℝ) (252263268313/500000000000 : ℝ) (248748602079/500000000000 : ℝ) (248748602083/500000000000 : ℝ) (125252967597/250000000000 : ℝ) (125252967599/250000000000 : ℝ) (250499771153/500000000000 : ℝ) (100199908463/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 3 (125252967597/250000000000 : ℝ) (125252967599/250000000000 : ℝ) (250499771153/500000000000 : ℝ) (100199908463/200000000000 : ℝ) (501005706347/1000000000000 : ℝ) (125251426589/250000000000 : ℝ) (501005706309/1000000000000 : ℝ) (250502853159/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 4 (501005706347/1000000000000 : ℝ) (125251426589/250000000000 : ℝ) (501005706309/1000000000000 : ℝ) (250502853159/500000000000 : ℝ) (62625713291/125000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 5 (62625713291/125000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 6 (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8335/65536 : ℝ))) 7 (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8335/65536 : ℝ)) hmem 8 (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8335/65536 : ℝ))) hcmem 8 (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8335/65536 : ℝ)) (992098304451/1000000000000 : ℝ) (496049152227/500000000000 : ℝ) (501005706327/1000000000000 : ℝ) (501005706337/1000000000000 : ℝ) (396622955441/500000000000 : ℝ) (793245910901/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0607_exp_lower
  have heNumeric : (2054902804411/1000000000000 : ℝ)/4 ≤ Real.exp (-85256423860953/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902804411/1000000000000 : ℝ)/4 ≤ Real.exp ((66679/524288 : ℝ)-(793245910901/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66679/524288 : ℝ) (8335/65536 : ℝ) (793245910901/1000000000000 : ℝ) (2054902804411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0608; no trusted numerical premise.
theorem cover8_leaf0608_exp_radius : (998014724612139369/1000000000000000000 : ℝ) ≤ Real.exp ((-66681/4194304 : ℝ)/8) ∧ Real.exp ((-66681/4194304 : ℝ)/8) ≤ (99801472461213937/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66681/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0608_exp_lower : (920113518351410749/1000000000000000000 : ℝ) ≤ Real.exp ((-10657053060929/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657053060929/16000000000000 : ℝ)/8) ≤ (3680454073405643/4000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657053060929/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0608_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902794353/1000000000000 : ℝ) ≤ 4*Real.exp (8335/65536 : ℝ)*Real.exp (-mu (radius 8 (66681/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902794353/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66681/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0608_exp_radius
  have hrNumeric : (984227716719/1000000000000 : ℝ) ≤ Real.exp (-66681/4194304 : ℝ) ∧ Real.exp (-66681/4194304 : ℝ) ≤ (12302846459/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984227716719/1000000000000 : ℝ) ≤ (radius 8 (66681/524288 : ℝ)) ∧ (radius 8 (66681/524288 : ℝ)) ≤ (12302846459/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66681/524288 : ℝ)) (984227716719/1000000000000 : ℝ) (12302846459/12500000000 : ℝ) (35381238893/200000000000 : ℝ) (176906194471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66681/524288 : ℝ)) (984227716719/1000000000000 : ℝ) (12302846459/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984227716719/1000000000000 : ℝ) (12302846459/12500000000 : ℝ) (992113858359/1000000000000 : ℝ) (24802846459/25000000000 : ℝ) (39683300603/40000000000 : ℝ) (992082515077/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 1 (992113858359/1000000000000 : ℝ) (24802846459/25000000000 : ℝ) (39683300603/40000000000 : ℝ) (992082515077/1000000000000 : ℝ) (992098186717/1000000000000 : ℝ) (992098186719/1000000000000 : ℝ) (992098186593/1000000000000 : ℝ) (198419637319/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 2 (992098186717/1000000000000 : ℝ) (992098186719/1000000000000 : ℝ) (992098186593/1000000000000 : ℝ) (198419637319/200000000000 : ℝ) (198419637331/200000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 3 (198419637331/200000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 4 (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 5 (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 6 (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66681/524288 : ℝ)) 7 (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66681/524288 : ℝ))) (35381238893/200000000000 : ℝ) (176906194471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35381238893/200000000000 : ℝ) (176906194471/1000000000000 : ℝ) (36778318577/62500000000 : ℝ) (147113274309/250000000000 : ℝ) (84120436153/200000000000 : ℝ) (420602180773/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 1 (36778318577/62500000000 : ℝ) (147113274309/250000000000 : ℝ) (84120436153/200000000000 : ℝ) (420602180773/1000000000000 : ℝ) (252263819499/500000000000 : ℝ) (100905527801/200000000000 : ℝ) (12437459949/25000000000 : ℝ) (31093649873/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 2 (252263819499/500000000000 : ℝ) (100905527801/200000000000 : ℝ) (12437459949/25000000000 : ℝ) (31093649873/62500000000 : ℝ) (501013018479/1000000000000 : ℝ) (501013018487/1000000000000 : ℝ) (250500345373/500000000000 : ℝ) (250500345377/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 3 (501013018479/1000000000000 : ℝ) (501013018487/1000000000000 : ℝ) (250500345373/500000000000 : ℝ) (250500345377/500000000000 : ℝ) (125251713653/250000000000 : ℝ) (501006854621/1000000000000 : ℝ) (250503427287/500000000000 : ℝ) (501006854583/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 4 (125251713653/250000000000 : ℝ) (501006854621/1000000000000 : ℝ) (250503427287/500000000000 : ℝ) (501006854583/1000000000000 : ℝ) (501006854593/1000000000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 5 (501006854593/1000000000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 6 (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66681/524288 : ℝ))) 7 (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66681/524288 : ℝ)) hmem 8 (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66681/524288 : ℝ))) hcmem 8 (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66681/524288 : ℝ)) (496049093327/500000000000 : ℝ) (992098186657/1000000000000 : ℝ) (7828232103/15625000000 : ℝ) (250503427301/500000000000 : ℝ) (1269196517/1600000000 : ℝ) (99155977893/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0608_exp_lower
  have heNumeric : (2054902794353/1000000000000 : ℝ)/4 ≤ Real.exp (-10657053060929/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902794353/1000000000000 : ℝ)/4 ≤ Real.exp ((8335/65536 : ℝ)-(99155977893/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8335/65536 : ℝ) (66681/524288 : ℝ) (99155977893/125000000000 : ℝ) (2054902794353/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0609; no trusted numerical premise.
theorem cover8_leaf0609_exp_radius : (499007347434491621/500000000000000000 : ℝ) ≤ Real.exp ((-33341/2097152 : ℝ)/8) ∧ Real.exp ((-33341/2097152 : ℝ)/8) ≤ (998014694868983243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33341/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0609_exp_lower : (460056758895337171/500000000000000000 : ℝ) ≤ Real.exp ((-85256425111479/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256425111479/128000000000000 : ℝ)/8) ≤ (920113517790674343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256425111479/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0609_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980556867/200000000000 : ℝ) ≤ 4*Real.exp (66681/524288 : ℝ)*Real.exp (-mu (radius 8 (33341/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980556867/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33341/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0609_exp_radius
  have hrNumeric : (984227482061/1000000000000 : ℝ) ≤ Real.exp (-33341/2097152 : ℝ) ∧ Real.exp (-33341/2097152 : ℝ) ≤ (492113741031/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984227482061/1000000000000 : ℝ) ≤ (radius 8 (33341/262144 : ℝ)) ∧ (radius 8 (33341/262144 : ℝ)) ≤ (492113741031/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33341/262144 : ℝ)) (984227482061/1000000000000 : ℝ) (492113741031/500000000000 : ℝ) (176907499993/1000000000000 : ℝ) (176907499999/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33341/262144 : ℝ)) (984227482061/1000000000000 : ℝ) (492113741031/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984227482061/1000000000000 : ℝ) (492113741031/500000000000 : ℝ) (99211374103/100000000000 : ℝ) (992113741031/1000000000000 : ℝ) (99208239681/100000000000 : ℝ) (992082396811/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 1 (99211374103/100000000000 : ℝ) (992113741031/1000000000000 : ℝ) (99208239681/100000000000 : ℝ) (992082396811/1000000000000 : ℝ) (24802451723/25000000000 : ℝ) (992098068921/1000000000000 : ℝ) (248024517199/250000000000 : ℝ) (496049034399/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 2 (24802451723/25000000000 : ℝ) (992098068921/1000000000000 : ℝ) (248024517199/250000000000 : ℝ) (496049034399/500000000000 : ℝ) (496049034429/500000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 3 (496049034429/500000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 4 (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 5 (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 6 (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33341/262144 : ℝ)) 7 (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33341/262144 : ℝ))) (176907499993/1000000000000 : ℝ) (176907499999/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176907499993/1000000000000 : ℝ) (176907499999/1000000000000 : ℝ) (147113437499/250000000000 : ℝ) (470763/800000 : ℝ) (420603732737/1000000000000 : ℝ) (84120746549/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 1 (147113437499/250000000000 : ℝ) (470763/800000 : ℝ) (420603732737/1000000000000 : ℝ) (84120746549/200000000000 : ℝ) (252264370683/500000000000 : ℝ) (504528741373/1000000000000 : ℝ) (497499591749/1000000000000 : ℝ) (497499591757/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 2 (252264370683/500000000000 : ℝ) (504528741373/1000000000000 : ℝ) (497499591749/1000000000000 : ℝ) (497499591757/1000000000000 : ℝ) (501014166557/1000000000000 : ℝ) (100202833313/200000000000 : ℝ) (501001839173/1000000000000 : ℝ) (501001839181/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 3 (501014166557/1000000000000 : ℝ) (100202833313/200000000000 : ℝ) (501001839173/1000000000000 : ℝ) (501001839181/1000000000000 : ℝ) (100201600573/200000000000 : ℝ) (501008002873/1000000000000 : ℝ) (501008002827/1000000000000 : ℝ) (125252000709/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 4 (100201600573/200000000000 : ℝ) (501008002873/1000000000000 : ℝ) (501008002827/1000000000000 : ℝ) (125252000709/250000000000 : ℝ) (250504001423/500000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 5 (250504001423/500000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 6 (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33341/262144 : ℝ))) 7 (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33341/262144 : ℝ)) hmem 8 (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33341/262144 : ℝ))) hcmem 8 (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33341/262144 : ℝ)) (992098068857/1000000000000 : ℝ) (49604903443/50000000000 : ℝ) (100201600569/200000000000 : ℝ) (100201600571/200000000000 : ℝ) (793249735349/1000000000000 : ℝ) (99156216921/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0609_exp_lower
  have heNumeric : (410980556867/200000000000 : ℝ)/4 ≤ Real.exp (-85256425111479/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980556867/200000000000 : ℝ)/4 ≤ Real.exp ((66681/524288 : ℝ)-(99156216921/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66681/524288 : ℝ) (33341/262144 : ℝ) (99156216921/125000000000 : ℝ) (410980556867/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0610; no trusted numerical premise.
theorem cover8_leaf0610_exp_radius : (998014665125828001/1000000000000000000 : ℝ) ≤ Real.exp ((-66683/4194304 : ℝ)/8) ∧ Real.exp ((-66683/4194304 : ℝ)/8) ≤ (499007332562914001/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66683/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0610_exp_lower : (920113517232008191/1000000000000000000 : ℝ) ≤ Real.exp ((-42628212866611/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628212866611/64000000000000 : ℝ)/8) ≤ (898548356671883/976562500000000 : ℝ) := by
  have h := exp_small_bounds ((-42628212866611/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0610_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451387177/500000000000 : ℝ) ≤ 4*Real.exp (33341/262144 : ℝ)*Real.exp (-mu (radius 8 (66683/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451387177/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66683/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0610_exp_radius
  have hrNumeric : (984227247403/1000000000000 : ℝ) ≤ Real.exp (-66683/4194304 : ℝ) ∧ Real.exp (-66683/4194304 : ℝ) ≤ (246056811851/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984227247403/1000000000000 : ℝ) ≤ (radius 8 (66683/524288 : ℝ)) ∧ (radius 8 (66683/524288 : ℝ)) ≤ (246056811851/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66683/524288 : ℝ)) (984227247403/1000000000000 : ℝ) (246056811851/250000000000 : ℝ) (176908805511/1000000000000 : ℝ) (88454402759/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66683/524288 : ℝ)) (984227247403/1000000000000 : ℝ) (246056811851/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984227247403/1000000000000 : ℝ) (246056811851/250000000000 : ℝ) (992113623701/1000000000000 : ℝ) (496056811851/500000000000 : ℝ) (62005142409/62500000000 : ℝ) (496041139273/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 1 (992113623701/1000000000000 : ℝ) (496056811851/500000000000 : ℝ) (62005142409/62500000000 : ℝ) (496041139273/500000000000 : ℝ) (496048975561/500000000000 : ℝ) (248024487781/250000000000 : ℝ) (496048975499/500000000000 : ℝ) (992097951001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 2 (496048975561/500000000000 : ℝ) (248024487781/250000000000 : ℝ) (496048975499/500000000000 : ℝ) (992097951001/1000000000000 : ℝ) (49604897553/50000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 3 (49604897553/50000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 4 (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 5 (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 6 (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66683/524288 : ℝ)) 7 (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66683/524288 : ℝ))) (176908805511/1000000000000 : ℝ) (88454402759/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176908805511/1000000000000 : ℝ) (88454402759/500000000000 : ℝ) (117690880551/200000000000 : ℝ) (588454402759/1000000000000 : ℝ) (105151321173/250000000000 : ℝ) (420605284701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 1 (117690880551/200000000000 : ℝ) (588454402759/1000000000000 : ℝ) (105151321173/250000000000 : ℝ) (420605284701/1000000000000 : ℝ) (504529843723/1000000000000 : ℝ) (50452984373/100000000000 : ℝ) (248750392763/500000000000 : ℝ) (248750392767/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 2 (504529843723/1000000000000 : ℝ) (50452984373/100000000000 : ℝ) (248750392763/500000000000 : ℝ) (248750392767/500000000000 : ℝ) (7828364291/15625000000 : ℝ) (62626914329/125000000000 : ℝ) (501002987589/1000000000000 : ℝ) (501002987597/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 3 (7828364291/15625000000 : ℝ) (62626914329/125000000000 : ℝ) (501002987589/1000000000000 : ℝ) (501002987597/1000000000000 : ℝ) (250504575553/500000000000 : ℝ) (100201830223/200000000000 : ℝ) (125252287767/250000000000 : ℝ) (501009151077/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 4 (250504575553/500000000000 : ℝ) (100201830223/200000000000 : ℝ) (125252287767/250000000000 : ℝ) (501009151077/1000000000000 : ℝ) (501009151087/1000000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 5 (501009151087/1000000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 6 (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66683/524288 : ℝ))) 7 (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66683/524288 : ℝ)) hmem 8 (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66683/524288 : ℝ))) hcmem 8 (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66683/524288 : ℝ)) (992097951059/1000000000000 : ℝ) (992097951063/1000000000000 : ℝ) (250504575543/500000000000 : ℝ) (62626143887/125000000000 : ℝ) (396625823777/500000000000 : ℝ) (396625823787/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0610_exp_lower
  have heNumeric : (1027451387177/500000000000 : ℝ)/4 ≤ Real.exp (-42628212866611/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451387177/500000000000 : ℝ)/4 ≤ Real.exp ((33341/262144 : ℝ)-(396625823787/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33341/262144 : ℝ) (66683/524288 : ℝ) (396625823787/500000000000 : ℝ) (1027451387177/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0611; no trusted numerical premise.
theorem cover8_leaf0611_exp_radius : (499007317691336823/500000000000000000 : ℝ) ≤ Real.exp ((-16671/1048576 : ℝ)/8) ∧ Real.exp ((-16671/1048576 : ℝ)/8) ≤ (998014635382673647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16671/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0611_exp_lower : (92011351667552731/100000000000000000 : ℝ) ≤ Real.exp ((-85256426352533/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256426352533/128000000000000 : ℝ)/8) ≤ (920113516675527311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256426352533/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0611_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902764411/1000000000000 : ℝ) ≤ 4*Real.exp (66683/524288 : ℝ)*Real.exp (-mu (radius 8 (16671/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902764411/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16671/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0611_exp_radius
  have hrNumeric : (196845402549/200000000000 : ℝ) ≤ Real.exp (-16671/1048576 : ℝ) ∧ Real.exp (-16671/1048576 : ℝ) ≤ (492113506373/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196845402549/200000000000 : ℝ) ≤ (radius 8 (16671/131072 : ℝ)) ∧ (radius 8 (16671/131072 : ℝ)) ≤ (492113506373/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16671/131072 : ℝ)) (196845402549/200000000000 : ℝ) (492113506373/500000000000 : ℝ) (176910111019/1000000000000 : ℝ) (88455055513/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16671/131072 : ℝ)) (196845402549/200000000000 : ℝ) (492113506373/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196845402549/200000000000 : ℝ) (492113506373/500000000000 : ℝ) (248028376593/250000000000 : ℝ) (992113506373/1000000000000 : ℝ) (992082160279/1000000000000 : ℝ) (992082160281/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 1 (248028376593/250000000000 : ℝ) (992113506373/1000000000000 : ℝ) (992082160279/1000000000000 : ℝ) (992082160281/1000000000000 : ℝ) (39683913333/40000000000 : ℝ) (992097833327/1000000000000 : ℝ) (992097833201/1000000000000 : ℝ) (248024458301/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 2 (39683913333/40000000000 : ℝ) (992097833327/1000000000000 : ℝ) (992097833201/1000000000000 : ℝ) (248024458301/250000000000 : ℝ) (992097833263/1000000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 3 (992097833263/1000000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 4 (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 5 (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 6 (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16671/131072 : ℝ)) 7 (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16671/131072 : ℝ))) (176910111019/1000000000000 : ℝ) (88455055513/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176910111019/1000000000000 : ℝ) (88455055513/500000000000 : ℝ) (588455055509/1000000000000 : ℝ) (588455055513/1000000000000 : ℝ) (105151709157/250000000000 : ℝ) (210303418319/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 1 (588455055509/1000000000000 : ℝ) (588455055513/1000000000000 : ℝ) (105151709157/250000000000 : ℝ) (210303418319/500000000000 : ℝ) (126132736517/250000000000 : ℝ) (126132736519/250000000000 : ℝ) (497501979287/1000000000000 : ℝ) (15546936853/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 2 (126132736517/250000000000 : ℝ) (126132736519/250000000000 : ℝ) (497501979287/1000000000000 : ℝ) (15546936853/31250000000 : ℝ) (501016462677/1000000000000 : ℝ) (250508231343/500000000000 : ℝ) (501004135991/1000000000000 : ℝ) (62625517/125000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 3 (501016462677/1000000000000 : ℝ) (250508231343/500000000000 : ℝ) (501004135991/1000000000000 : ℝ) (62625517/125000000 : ℝ) (250505149667/500000000000 : ℝ) (501010299343/1000000000000 : ℝ) (15656571853/31250000000 : ℝ) (250505149653/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 4 (250505149667/500000000000 : ℝ) (501010299343/1000000000000 : ℝ) (15656571853/31250000000 : ℝ) (250505149653/500000000000 : ℝ) (100202059863/200000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 5 (100202059863/200000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 6 (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16671/131072 : ℝ))) 7 (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16671/131072 : ℝ)) hmem 8 (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16671/131072 : ℝ))) hcmem 8 (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16671/131072 : ℝ)) (496048916631/500000000000 : ℝ) (496048916633/500000000000 : ℝ) (250505149657/500000000000 : ℝ) (20040411973/40000000000 : ℝ) (39662677987/50000000000 : ℝ) (793253559761/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0611_exp_lower
  have heNumeric : (2054902764411/1000000000000 : ℝ)/4 ≤ Real.exp (-85256426352533/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902764411/1000000000000 : ℝ)/4 ≤ Real.exp ((66683/524288 : ℝ)-(793253559761/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66683/524288 : ℝ) (16671/131072 : ℝ) (793253559761/1000000000000 : ℝ) (2054902764411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0612; no trusted numerical premise.
theorem cover8_leaf0612_exp_radius : (499007302819760089/500000000000000000 : ℝ) ≤ Real.exp ((-66685/4194304 : ℝ)/8) ∧ Real.exp ((-66685/4194304 : ℝ)/8) ≤ (998014605639520179/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66685/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0612_exp_lower : (920113516121346713/1000000000000000000 : ℝ) ≤ Real.exp ((-21314106742321/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314106742321/32000000000000 : ℝ)/8) ≤ (460056758060673357/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314106742321/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0612_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490275451/100000000000 : ℝ) ≤ 4*Real.exp (16671/131072 : ℝ)*Real.exp (-mu (radius 8 (66685/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490275451/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66685/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0612_exp_radius
  have hrNumeric : (984226778087/1000000000000 : ℝ) ≤ Real.exp (-66685/4194304 : ℝ) ∧ Real.exp (-66685/4194304 : ℝ) ≤ (123028347261/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984226778087/1000000000000 : ℝ) ≤ (radius 8 (66685/524288 : ℝ)) ∧ (radius 8 (66685/524288 : ℝ)) ≤ (123028347261/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66685/524288 : ℝ)) (984226778087/1000000000000 : ℝ) (123028347261/125000000000 : ℝ) (88455708259/500000000000 : ℝ) (44227854131/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66685/524288 : ℝ)) (984226778087/1000000000000 : ℝ) (123028347261/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984226778087/1000000000000 : ℝ) (123028347261/125000000000 : ℝ) (992113389043/1000000000000 : ℝ) (248028347261/250000000000 : ℝ) (496041021007/500000000000 : ℝ) (198416408403/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 1 (992113389043/1000000000000 : ℝ) (248028347261/250000000000 : ℝ) (496041021007/500000000000 : ℝ) (198416408403/200000000000 : ℝ) (124012214441/125000000000 : ℝ) (99209771553/100000000000 : ℝ) (248024428851/250000000000 : ℝ) (496048857703/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 2 (124012214441/125000000000 : ℝ) (99209771553/100000000000 : ℝ) (248024428851/250000000000 : ℝ) (496048857703/500000000000 : ℝ) (496048857733/500000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 3 (496048857733/500000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 4 (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 5 (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 6 (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66685/524288 : ℝ)) 7 (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66685/524288 : ℝ))) (88455708259/500000000000 : ℝ) (44227854131/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88455708259/500000000000 : ℝ) (44227854131/250000000000 : ℝ) (588455708259/1000000000000 : ℝ) (294227854131/500000000000 : ℝ) (420608388549/1000000000000 : ℝ) (420608388557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 1 (588455708259/1000000000000 : ℝ) (294227854131/500000000000 : ℝ) (420608388549/1000000000000 : ℝ) (420608388557/1000000000000 : ℝ) (126133012101/250000000000 : ℝ) (50453204841/100000000000 : ℝ) (248751586519/500000000000 : ℝ) (99500634609/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 2 (126133012101/250000000000 : ℝ) (50453204841/100000000000 : ℝ) (248751586519/500000000000 : ℝ) (99500634609/200000000000 : ℝ) (501017610721/1000000000000 : ℝ) (62627201341/125000000000 : ℝ) (501005284383/1000000000000 : ℝ) (501005284391/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 3 (501017610721/1000000000000 : ℝ) (62627201341/125000000000 : ℝ) (501005284383/1000000000000 : ℝ) (501005284391/1000000000000 : ℝ) (1957075967/3906250000 : ℝ) (12525286189/25000000000 : ℝ) (250505723757/500000000000 : ℝ) (250505723761/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 4 (1957075967/3906250000 : ℝ) (12525286189/25000000000 : ℝ) (250505723757/500000000000 : ℝ) (250505723761/500000000000 : ℝ) (501011447533/1000000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 5 (501011447533/1000000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 6 (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66685/524288 : ℝ))) 7 (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66685/524288 : ℝ)) hmem 8 (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66685/524288 : ℝ))) hcmem 8 (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66685/524288 : ℝ)) (198419543093/200000000000 : ℝ) (248024428867/250000000000 : ℝ) (125252861883/250000000000 : ℝ) (501011447541/1000000000000 : ℝ) (793255471911/1000000000000 : ℝ) (99156933991/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0612_exp_lower
  have heNumeric : (205490275451/100000000000 : ℝ)/4 ≤ Real.exp (-21314106742321/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490275451/100000000000 : ℝ)/4 ≤ Real.exp ((16671/131072 : ℝ)-(99156933991/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16671/131072 : ℝ) (66685/524288 : ℝ) (99156933991/125000000000 : ℝ) (205490275451/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0613; no trusted numerical premise.
theorem cover8_leaf0613_exp_radius : (249503643974091899/250000000000000000 : ℝ) ≤ Real.exp ((-33343/2097152 : ℝ)/8) ∧ Real.exp ((-33343/2097152 : ℝ)/8) ≤ (998014575896367597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33343/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0613_exp_lower : (460056757784560679/500000000000000000 : ℝ) ≤ Real.exp ((-85256427583859/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256427583859/128000000000000 : ℝ)/8) ≤ (920113515569121359/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256427583859/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0613_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725686161/250000000000 : ℝ) ≤ 4*Real.exp (66685/524288 : ℝ)*Real.exp (-mu (radius 8 (33343/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725686161/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33343/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0613_exp_radius
  have hrNumeric : (984226543429/1000000000000 : ℝ) ≤ Real.exp (-33343/2097152 : ℝ) ∧ Real.exp (-33343/2097152 : ℝ) ≤ (98422654343/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984226543429/1000000000000 : ℝ) ≤ (radius 8 (33343/262144 : ℝ)) ∧ (radius 8 (33343/262144 : ℝ)) ≤ (98422654343/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33343/262144 : ℝ)) (984226543429/1000000000000 : ℝ) (98422654343/100000000000 : ℝ) (88456361003/500000000000 : ℝ) (176912722013/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33343/262144 : ℝ)) (984226543429/1000000000000 : ℝ) (98422654343/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984226543429/1000000000000 : ℝ) (98422654343/100000000000 : ℝ) (496056635857/500000000000 : ℝ) (198422654343/200000000000 : ℝ) (248020480937/250000000000 : ℝ) (793665539/800000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 1 (496056635857/500000000000 : ℝ) (198422654343/200000000000 : ℝ) (248020480937/250000000000 : ℝ) (793665539/800000000 : ℝ) (992097597731/1000000000000 : ℝ) (992097597733/1000000000000 : ℝ) (992097597607/1000000000000 : ℝ) (992097597609/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 2 (992097597731/1000000000000 : ℝ) (992097597733/1000000000000 : ℝ) (992097597607/1000000000000 : ℝ) (992097597609/1000000000000 : ℝ) (992097597669/1000000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 3 (992097597669/1000000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 4 (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 5 (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 6 (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33343/262144 : ℝ)) 7 (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33343/262144 : ℝ))) (88456361003/500000000000 : ℝ) (176912722013/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88456361003/500000000000 : ℝ) (176912722013/1000000000000 : ℝ) (588456361003/1000000000000 : ℝ) (588456361007/1000000000000 : ℝ) (8412198809/20000000000 : ℝ) (21030497023/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 1 (588456361003/1000000000000 : ℝ) (588456361007/1000000000000 : ℝ) (8412198809/20000000000 : ℝ) (21030497023/50000000000 : ℝ) (252266575363/500000000000 : ℝ) (252266575367/500000000000 : ℝ) (497504366773/1000000000000 : ℝ) (248752183391/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 2 (252266575363/500000000000 : ℝ) (252266575367/500000000000 : ℝ) (497504366773/1000000000000 : ℝ) (248752183391/500000000000 : ℝ) (501018758749/1000000000000 : ℝ) (250509379379/500000000000 : ℝ) (501006432761/1000000000000 : ℝ) (50100643277/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 3 (501018758749/1000000000000 : ℝ) (250509379379/500000000000 : ℝ) (501006432761/1000000000000 : ℝ) (50100643277/100000000000 : ℝ) (100202519151/200000000000 : ℝ) (125253148941/250000000000 : ℝ) (501012595717/1000000000000 : ℝ) (501012595727/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 4 (100202519151/200000000000 : ℝ) (125253148941/250000000000 : ℝ) (501012595717/1000000000000 : ℝ) (501012595727/1000000000000 : ℝ) (62626574467/125000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 5 (62626574467/125000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 6 (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33343/262144 : ℝ))) 7 (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33343/262144 : ℝ)) hmem 8 (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33343/262144 : ℝ))) hcmem 8 (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33343/262144 : ℝ)) (248024399417/250000000000 : ℝ) (992097597671/1000000000000 : ℝ) (100202519147/200000000000 : ℝ) (250506297873/500000000000 : ℝ) (793257384057/1000000000000 : ℝ) (396628692039/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0613_exp_lower
  have heNumeric : (513725686161/250000000000 : ℝ)/4 ≤ Real.exp (-85256427583859/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725686161/250000000000 : ℝ)/4 ≤ Real.exp ((66685/524288 : ℝ)-(396628692039/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66685/524288 : ℝ) (33343/262144 : ℝ) (396628692039/500000000000 : ℝ) (513725686161/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0614; no trusted numerical premise.
theorem cover8_leaf0614_exp_radius : (998014546153215901/1000000000000000000 : ℝ) ≤ Real.exp ((-66687/4194304 : ℝ)/8) ∧ Real.exp ((-66687/4194304 : ℝ)/8) ≤ (499007273076607951/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66687/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0614_exp_lower : (184022703003885263/200000000000000000 : ℝ) ≤ Real.exp ((-42628214097809/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628214097809/64000000000000 : ℝ)/8) ≤ (230028378754856579/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628214097809/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0614_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451367411/500000000000 : ℝ) ≤ 4*Real.exp (33343/262144 : ℝ)*Real.exp (-mu (radius 8 (66687/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451367411/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66687/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0614_exp_radius
  have hrNumeric : (984226308771/1000000000000 : ℝ) ≤ Real.exp (-66687/4194304 : ℝ) ∧ Real.exp (-66687/4194304 : ℝ) ≤ (246056577193/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984226308771/1000000000000 : ℝ) ≤ (radius 8 (66687/524288 : ℝ)) ∧ (radius 8 (66687/524288 : ℝ)) ≤ (246056577193/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66687/524288 : ℝ)) (984226308771/1000000000000 : ℝ) (246056577193/250000000000 : ℝ) (35382805497/200000000000 : ℝ) (176914027491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66687/524288 : ℝ)) (984226308771/1000000000000 : ℝ) (246056577193/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984226308771/1000000000000 : ℝ) (246056577193/250000000000 : ℝ) (198422630877/200000000000 : ℝ) (496056577193/500000000000 : ℝ) (992081805483/1000000000000 : ℝ) (248020451371/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 1 (198422630877/200000000000 : ℝ) (496056577193/500000000000 : ℝ) (992081805483/1000000000000 : ℝ) (248020451371/250000000000 : ℝ) (496048739967/500000000000 : ℝ) (198419495987/200000000000 : ℝ) (99209747981/100000000000 : ℝ) (248024369953/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 2 (496048739967/500000000000 : ℝ) (198419495987/200000000000 : ℝ) (99209747981/100000000000 : ℝ) (248024369953/250000000000 : ℝ) (15501523123/15625000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 3 (15501523123/15625000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 4 (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 5 (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 6 (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66687/524288 : ℝ)) 7 (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66687/524288 : ℝ))) (35382805497/200000000000 : ℝ) (176914027491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35382805497/200000000000 : ℝ) (176914027491/1000000000000 : ℝ) (294228506871/500000000000 : ℝ) (294228506873/500000000000 : ℝ) (84122298467/200000000000 : ℝ) (420611492343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 1 (294228506871/500000000000 : ℝ) (294228506873/500000000000 : ℝ) (84122298467/200000000000 : ℝ) (420611492343/1000000000000 : ℝ) (252267126519/500000000000 : ℝ) (100906850609/200000000000 : ℝ) (31094097531/62500000000 : ℝ) (62188195063/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 2 (252267126519/500000000000 : ℝ) (100906850609/200000000000 : ℝ) (31094097531/62500000000 : ℝ) (62188195063/125000000000 : ℝ) (501019906767/1000000000000 : ℝ) (20040796271/40000000000 : ℝ) (501007581127/1000000000000 : ℝ) (100201516227/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 3 (501019906767/1000000000000 : ℝ) (20040796271/40000000000 : ℝ) (501007581127/1000000000000 : ℝ) (100201516227/200000000000 : ℝ) (501013743947/1000000000000 : ℝ) (100202748791/200000000000 : ℝ) (501013743909/1000000000000 : ℝ) (250506871959/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 4 (501013743947/1000000000000 : ℝ) (100202748791/200000000000 : ℝ) (501013743909/1000000000000 : ℝ) (250506871959/500000000000 : ℝ) (62626717991/125000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 5 (62626717991/125000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 6 (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66687/524288 : ℝ))) 7 (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66687/524288 : ℝ)) hmem 8 (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66687/524288 : ℝ))) hcmem 8 (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66687/524288 : ℝ)) (992097479871/1000000000000 : ℝ) (496048739937/500000000000 : ℝ) (501013743927/1000000000000 : ℝ) (501013743937/1000000000000 : ℝ) (793259296187/1000000000000 : ℝ) (396629648103/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0614_exp_lower
  have heNumeric : (1027451367411/500000000000 : ℝ)/4 ≤ Real.exp (-42628214097809/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451367411/500000000000 : ℝ)/4 ≤ Real.exp ((33343/262144 : ℝ)-(396629648103/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33343/262144 : ℝ) (66687/524288 : ℝ) (396629648103/500000000000 : ℝ) (1027451367411/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0615; no trusted numerical premise.
theorem cover8_leaf0615_exp_radius : (249503629102516273/250000000000000000 : ℝ) ≤ Real.exp ((-521/32768 : ℝ)/8) ∧ Real.exp ((-521/32768 : ℝ)/8) ≤ (998014516410065093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-521/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0615_exp_lower : (920113514471686513/1000000000000000000 : ℝ) ≤ Real.exp ((-85256428805201/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256428805201/128000000000000 : ℝ)/8) ≤ (460056757235843257/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256428805201/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0615_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725681259/250000000000 : ℝ) ≤ 4*Real.exp (66687/524288 : ℝ)*Real.exp (-mu (radius 8 (521/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (513725681259/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (521/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0615_exp_radius
  have hrNumeric : (984226074113/1000000000000 : ℝ) ≤ Real.exp (-521/32768 : ℝ) ∧ Real.exp (-521/32768 : ℝ) ≤ (492113037057/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984226074113/1000000000000 : ℝ) ≤ (radius 8 (521/4096 : ℝ)) ∧ (radius 8 (521/4096 : ℝ)) ≤ (492113037057/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (521/4096 : ℝ)) (984226074113/1000000000000 : ℝ) (492113037057/500000000000 : ℝ) (176915332953/1000000000000 : ℝ) (1105720831/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (521/4096 : ℝ)) (984226074113/1000000000000 : ℝ) (492113037057/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (521/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984226074113/1000000000000 : ℝ) (492113037057/500000000000 : ℝ) (3875441551/3906250000 : ℝ) (992113037057/1000000000000 : ℝ) (992081687217/1000000000000 : ℝ) (992081687219/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (521/4096 : ℝ)) 1 (3875441551/3906250000 : ℝ) (992113037057/1000000000000 : ℝ) (992081687217/1000000000000 : ℝ) (992081687219/1000000000000 : ℝ) (124012170267/125000000000 : ℝ) (496048681069/500000000000 : ℝ) (248024340503/250000000000 : ℝ) (198419472403/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (521/4096 : ℝ)) 2 (124012170267/125000000000 : ℝ) (496048681069/500000000000 : ℝ) (248024340503/250000000000 : ℝ) (198419472403/200000000000 : ℝ) (496048681037/500000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (521/4096 : ℝ)) 3 (496048681037/500000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (521/4096 : ℝ)) 4 (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (521/4096 : ℝ)) 5 (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (521/4096 : ℝ)) 6 (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (521/4096 : ℝ)) 7 (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (521/4096 : ℝ))) (176915332953/1000000000000 : ℝ) (1105720831/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176915332953/1000000000000 : ℝ) (1105720831/6250000000 : ℝ) (147114416619/250000000000 : ℝ) (7355720831/12500000000 : ℝ) (210306522101/500000000000 : ℝ) (420613044211/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 1 (147114416619/250000000000 : ℝ) (7355720831/12500000000 : ℝ) (210306522101/500000000000 : ℝ) (420613044211/1000000000000 : ℝ) (504535355339/1000000000000 : ℝ) (252267677673/500000000000 : ℝ) (99501350841/200000000000 : ℝ) (497506754213/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 2 (504535355339/1000000000000 : ℝ) (252267677673/500000000000 : ℝ) (99501350841/200000000000 : ℝ) (497506754213/1000000000000 : ℝ) (125255263693/250000000000 : ℝ) (25051052739/50000000000 : ℝ) (501008729481/1000000000000 : ℝ) (501008729489/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 3 (125255263693/250000000000 : ℝ) (25051052739/50000000000 : ℝ) (501008729481/1000000000000 : ℝ) (501008729489/1000000000000 : ℝ) (250507446063/500000000000 : ℝ) (100202978427/200000000000 : ℝ) (62626861511/125000000000 : ℝ) (501014892097/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 4 (250507446063/500000000000 : ℝ) (100202978427/200000000000 : ℝ) (62626861511/125000000000 : ℝ) (501014892097/1000000000000 : ℝ) (501014892107/1000000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 5 (501014892107/1000000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 6 (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (521/4096 : ℝ))) 7 (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (521/4096 : ℝ)) hmem 8 (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (521/4096 : ℝ))) hcmem 8 (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (521/4096 : ℝ)) (992097362073/1000000000000 : ℝ) (992097362077/1000000000000 : ℝ) (250507446053/500000000000 : ℝ) (125253723029/250000000000 : ℝ) (793261208297/1000000000000 : ℝ) (793261208317/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0615_exp_lower
  have heNumeric : (513725681259/250000000000 : ℝ)/4 ≤ Real.exp (-85256428805201/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725681259/250000000000 : ℝ)/4 ≤ Real.exp ((66687/524288 : ℝ)-(793261208317/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66687/524288 : ℝ) (521/4096 : ℝ) (793261208317/1000000000000 : ℝ) (513725681259/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0616; no trusted numerical premise.
theorem cover8_leaf0616_exp_radius : (99801448666691517/100000000000000000 : ℝ) ≤ Real.exp ((-66689/4194304 : ℝ)/8) ∧ Real.exp ((-66689/4194304 : ℝ)/8) ≤ (998014486666915171/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66689/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0616_exp_lower : (230028378481561749/250000000000000000 : ℝ) ≤ Real.exp ((-666065854783/1000000000000 : ℝ)/8) ∧ Real.exp ((-666065854783/1000000000000 : ℝ)/8) ≤ (920113513926246997/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666065854783/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0616_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902715291/1000000000000 : ℝ) ≤ 4*Real.exp (521/4096 : ℝ)*Real.exp (-mu (radius 8 (66689/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902715291/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66689/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0616_exp_radius
  have hrNumeric : (196845167891/200000000000 : ℝ) ≤ Real.exp (-66689/4194304 : ℝ) ∧ Real.exp (-66689/4194304 : ℝ) ≤ (30757057483/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196845167891/200000000000 : ℝ) ≤ (radius 8 (66689/524288 : ℝ)) ∧ (radius 8 (66689/524288 : ℝ)) ≤ (30757057483/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66689/524288 : ℝ)) (196845167891/200000000000 : ℝ) (30757057483/31250000000 : ℝ) (44229159603/250000000000 : ℝ) (88458319209/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66689/524288 : ℝ)) (196845167891/200000000000 : ℝ) (30757057483/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196845167891/200000000000 : ℝ) (30757057483/31250000000 : ℝ) (992112919727/1000000000000 : ℝ) (62007057483/62500000000 : ℝ) (124010196119/125000000000 : ℝ) (992081568953/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 1 (992112919727/1000000000000 : ℝ) (62007057483/62500000000 : ℝ) (124010196119/125000000000 : ℝ) (992081568953/1000000000000 : ℝ) (992097244339/1000000000000 : ℝ) (992097244341/1000000000000 : ℝ) (198419448843/200000000000 : ℝ) (992097244217/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 2 (992097244339/1000000000000 : ℝ) (992097244341/1000000000000 : ℝ) (198419448843/200000000000 : ℝ) (992097244217/1000000000000 : ℝ) (992097244277/1000000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 3 (992097244277/1000000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 4 (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 5 (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 6 (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66689/524288 : ℝ)) 7 (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66689/524288 : ℝ))) (44229159603/250000000000 : ℝ) (88458319209/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44229159603/250000000000 : ℝ) (88458319209/500000000000 : ℝ) (294229159603/500000000000 : ℝ) (588458319209/1000000000000 : ℝ) (105153649013/250000000000 : ℝ) (21030729803/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 1 (294229159603/500000000000 : ℝ) (588458319209/1000000000000 : ℝ) (105153649013/250000000000 : ℝ) (21030729803/50000000000 : ℝ) (504536457629/1000000000000 : ℝ) (100907291527/200000000000 : ℝ) (248753973951/500000000000 : ℝ) (497507947909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 2 (504536457629/1000000000000 : ℝ) (100907291527/200000000000 : ℝ) (248753973951/500000000000 : ℝ) (497507947909/1000000000000 : ℝ) (100204440553/200000000000 : ℝ) (125255550693/250000000000 : ℝ) (501009877823/1000000000000 : ℝ) (501009877831/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 3 (100204440553/200000000000 : ℝ) (125255550693/250000000000 : ℝ) (501009877823/1000000000000 : ℝ) (501009877831/1000000000000 : ℝ) (250508020147/500000000000 : ℝ) (250508020151/500000000000 : ℝ) (7828375629/15625000000 : ℝ) (62627005033/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 4 (250508020147/500000000000 : ℝ) (250508020151/500000000000 : ℝ) (7828375629/15625000000 : ℝ) (62627005033/125000000000 : ℝ) (20040641611/40000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 5 (20040641611/40000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 6 (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66689/524288 : ℝ))) 7 (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66689/524288 : ℝ)) hmem 8 (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66689/524288 : ℝ))) hcmem 8 (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66689/524288 : ℝ)) (248024311069/250000000000 : ℝ) (992097244279/1000000000000 : ℝ) (250508020137/500000000000 : ℝ) (501016040283/1000000000000 : ℝ) (79326312039/100000000000 : ℝ) (99157890051/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0616_exp_lower
  have heNumeric : (2054902715291/1000000000000 : ℝ)/4 ≤ Real.exp (-666065854783/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902715291/1000000000000 : ℝ)/4 ≤ Real.exp ((521/4096 : ℝ)-(99157890051/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (521/4096 : ℝ) (66689/524288 : ℝ) (99157890051/125000000000 : ℝ) (2054902715291/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0617; no trusted numerical premise.
theorem cover8_leaf0617_exp_radius : (499007228461883067/500000000000000000 : ℝ) ≤ Real.exp ((-33345/2097152 : ℝ)/8) ∧ Real.exp ((-33345/2097152 : ℝ)/8) ≤ (199602891384753227/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33345/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0617_exp_lower : (230028378345748187/250000000000000000 : ℝ) ≤ Real.exp ((-17051286003363/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051286003363/25600000000000 : ℝ)/8) ≤ (920113513382992749/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051286003363/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0617_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980541117/200000000000 : ℝ) ≤ 4*Real.exp (66689/524288 : ℝ)*Real.exp (-mu (radius 8 (33345/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980541117/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33345/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0617_exp_radius
  have hrNumeric : (984225604797/1000000000000 : ℝ) ≤ Real.exp (-33345/2097152 : ℝ) ∧ Real.exp (-33345/2097152 : ℝ) ≤ (492112802399/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984225604797/1000000000000 : ℝ) ≤ (radius 8 (33345/262144 : ℝ)) ∧ (radius 8 (33345/262144 : ℝ)) ≤ (492112802399/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33345/262144 : ℝ)) (984225604797/1000000000000 : ℝ) (492112802399/500000000000 : ℝ) (176917943861/1000000000000 : ℝ) (176917943867/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33345/262144 : ℝ)) (984225604797/1000000000000 : ℝ) (492112802399/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984225604797/1000000000000 : ℝ) (492112802399/500000000000 : ℝ) (496056401199/500000000000 : ℝ) (992112802399/1000000000000 : ℝ) (496040725343/500000000000 : ℝ) (15501272667/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 1 (496056401199/500000000000 : ℝ) (992112802399/1000000000000 : ℝ) (496040725343/500000000000 : ℝ) (15501272667/15625000000 : ℝ) (496048563271/500000000000 : ℝ) (62006070409/62500000000 : ℝ) (496048563209/500000000000 : ℝ) (49604856321/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 2 (496048563271/500000000000 : ℝ) (62006070409/62500000000 : ℝ) (496048563209/500000000000 : ℝ) (49604856321/50000000000 : ℝ) (12401214081/12500000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 3 (12401214081/12500000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 4 (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 5 (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 6 (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33345/262144 : ℝ)) 7 (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33345/262144 : ℝ))) (176917943861/1000000000000 : ℝ) (176917943867/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176917943861/1000000000000 : ℝ) (176917943867/1000000000000 : ℝ) (58845897193/100000000000 : ℝ) (294229485967/500000000000 : ℝ) (105154036971/250000000000 : ℝ) (105154036973/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 1 (58845897193/100000000000 : ℝ) (294229485967/500000000000 : ℝ) (105154036971/250000000000 : ℝ) (105154036973/250000000000 : ℝ) (504537559907/1000000000000 : ℝ) (504537559913/1000000000000 : ℝ) (99501828317/200000000000 : ℝ) (62188642699/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 2 (504537559907/1000000000000 : ℝ) (504537559913/1000000000000 : ℝ) (99501828317/200000000000 : ℝ) (62188642699/125000000000 : ℝ) (250511675373/500000000000 : ℝ) (501023350753/1000000000000 : ℝ) (62626378269/125000000000 : ℝ) (6262637827/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 3 (250511675373/500000000000 : ℝ) (501023350753/1000000000000 : ℝ) (62626378269/125000000000 : ℝ) (6262637827/12500000000 : ℝ) (501017188449/1000000000000 : ℝ) (501017188457/1000000000000 : ℝ) (501017188411/1000000000000 : ℝ) (501017188419/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 4 (501017188449/1000000000000 : ℝ) (501017188457/1000000000000 : ℝ) (501017188411/1000000000000 : ℝ) (501017188419/1000000000000 : ℝ) (50101718843/100000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 5 (50101718843/100000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 6 (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33345/262144 : ℝ))) 7 (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33345/262144 : ℝ)) hmem 8 (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33345/262144 : ℝ))) hcmem 8 (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33345/262144 : ℝ)) (992097126479/1000000000000 : ℝ) (496048563241/500000000000 : ℝ) (501017188429/1000000000000 : ℝ) (250508594219/500000000000 : ℝ) (793265032463/1000000000000 : ℝ) (4957906453/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0617_exp_lower
  have heNumeric : (410980541117/200000000000 : ℝ)/4 ≤ Real.exp (-17051286003363/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980541117/200000000000 : ℝ)/4 ≤ Real.exp ((66689/524288 : ℝ)-(4957906453/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66689/524288 : ℝ) (33345/262144 : ℝ) (4957906453/6250000000 : ℝ) (410980541117/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0618; no trusted numerical premise.
theorem cover8_leaf0618_exp_radius : (3898493856174289/3906250000000000 : ℝ) ≤ Real.exp ((-66691/4194304 : ℝ)/8) ∧ Real.exp ((-66691/4194304 : ℝ)/8) ≤ (199602885436123597/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66691/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0618_exp_lower : (92011351284272887/100000000000000000 : ℝ) ≤ Real.exp ((-42628215309039/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628215309039/64000000000000 : ℝ)/8) ≤ (920113512842728871/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628215309039/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0618_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725673983/250000000000 : ℝ) ≤ 4*Real.exp (33345/262144 : ℝ)*Real.exp (-mu (radius 8 (66691/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725673983/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66691/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0618_exp_radius
  have hrNumeric : (49211268507/50000000000 : ℝ) ≤ Real.exp (-66691/4194304 : ℝ) ∧ Real.exp (-66691/4194304 : ℝ) ≤ (984225370141/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49211268507/50000000000 : ℝ) ≤ (radius 8 (66691/524288 : ℝ)) ∧ (radius 8 (66691/524288 : ℝ)) ≤ (984225370141/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66691/524288 : ℝ)) (49211268507/50000000000 : ℝ) (984225370141/1000000000000 : ℝ) (88459624647/500000000000 : ℝ) (1769192493/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66691/524288 : ℝ)) (49211268507/50000000000 : ℝ) (984225370141/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49211268507/50000000000 : ℝ) (984225370141/1000000000000 : ℝ) (99211268507/100000000000 : ℝ) (992112685071/1000000000000 : ℝ) (992081332421/1000000000000 : ℝ) (992081332423/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 1 (99211268507/100000000000 : ℝ) (992112685071/1000000000000 : ℝ) (992081332421/1000000000000 : ℝ) (992081332423/1000000000000 : ℝ) (198419401749/200000000000 : ℝ) (992097008747/1000000000000 : ℝ) (992097008621/1000000000000 : ℝ) (62006063039/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 2 (198419401749/200000000000 : ℝ) (992097008747/1000000000000 : ℝ) (992097008621/1000000000000 : ℝ) (62006063039/62500000000 : ℝ) (992097008683/1000000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 3 (992097008683/1000000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 4 (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 5 (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 6 (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66691/524288 : ℝ)) 7 (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66691/524288 : ℝ))) (88459624647/500000000000 : ℝ) (1769192493/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88459624647/500000000000 : ℝ) (1769192493/10000000000 : ℝ) (588459624647/1000000000000 : ℝ) (11769192493/20000000000 : ℝ) (420617699691/1000000000000 : ℝ) (420617699699/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 1 (588459624647/1000000000000 : ℝ) (11769192493/20000000000 : ℝ) (420617699691/1000000000000 : ℝ) (420617699699/1000000000000 : ℝ) (504538662169/1000000000000 : ℝ) (20181546487/40000000000 : ℝ) (497510335249/1000000000000 : ℝ) (62188791907/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 2 (504538662169/1000000000000 : ℝ) (20181546487/40000000000 : ℝ) (497510335249/1000000000000 : ℝ) (62188791907/125000000000 : ℝ) (501024498709/1000000000000 : ℝ) (125256124679/250000000000 : ℝ) (3914157613/7812500000 : ℝ) (62626521809/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 3 (501024498709/1000000000000 : ℝ) (125256124679/250000000000 : ℝ) (3914157613/7812500000 : ℝ) (62626521809/125000000000 : ℝ) (250509168293/500000000000 : ℝ) (250509168297/500000000000 : ℝ) (125254584137/250000000000 : ℝ) (501018336557/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 4 (250509168293/500000000000 : ℝ) (250509168297/500000000000 : ℝ) (125254584137/250000000000 : ℝ) (501018336557/1000000000000 : ℝ) (501018336567/1000000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 5 (501018336567/1000000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 6 (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66691/524288 : ℝ))) 7 (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66691/524288 : ℝ)) hmem 8 (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66691/524288 : ℝ))) hcmem 8 (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66691/524288 : ℝ)) (496048504341/500000000000 : ℝ) (496048504343/500000000000 : ℝ) (250509168283/500000000000 : ℝ) (7828411509/15625000000 : ℝ) (396633472253/500000000000 : ℝ) (396633472263/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0618_exp_lower
  have heNumeric : (513725673983/250000000000 : ℝ)/4 ≤ Real.exp (-42628215309039/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725673983/250000000000 : ℝ)/4 ≤ Real.exp ((33345/262144 : ℝ)-(396633472263/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33345/262144 : ℝ) (66691/524288 : ℝ) (396633472263/500000000000 : ℝ) (513725673983/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0619; no trusted numerical premise.
theorem cover8_leaf0619_exp_radius : (998014397437470721/1000000000000000000 : ℝ) ≤ Real.exp ((-16673/1048576 : ℝ)/8) ∧ Real.exp ((-16673/1048576 : ℝ)/8) ≤ (499007198718735361/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16673/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0619_exp_lower : (920113512303845163/1000000000000000000 : ℝ) ≤ Real.exp ((-17051286243561/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051286243561/25600000000000 : ℝ)/8) ≤ (230028378075961291/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051286243561/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0619_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215708947/31250000000 : ℝ) ≤ 4*Real.exp (66691/524288 : ℝ)*Real.exp (-mu (radius 8 (16673/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215708947/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16673/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0619_exp_radius
  have hrNumeric : (492112567741/500000000000 : ℝ) ≤ Real.exp (-16673/1048576 : ℝ) ∧ Real.exp (-16673/1048576 : ℝ) ≤ (984225135483/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492112567741/500000000000 : ℝ) ≤ (radius 8 (16673/131072 : ℝ)) ∧ (radius 8 (16673/131072 : ℝ)) ≤ (984225135483/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16673/131072 : ℝ)) (492112567741/500000000000 : ℝ) (984225135483/1000000000000 : ℝ) (88460277361/500000000000 : ℝ) (176920554729/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16673/131072 : ℝ)) (492112567741/500000000000 : ℝ) (984225135483/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492112567741/500000000000 : ℝ) (984225135483/1000000000000 : ℝ) (992112567741/1000000000000 : ℝ) (496056283871/500000000000 : ℝ) (248020303539/250000000000 : ℝ) (992081214157/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 1 (992112567741/1000000000000 : ℝ) (496056283871/500000000000 : ℝ) (248020303539/250000000000 : ℝ) (992081214157/1000000000000 : ℝ) (248024222737/250000000000 : ℝ) (19841937819/20000000000 : ℝ) (124012111353/125000000000 : ℝ) (496048445413/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 2 (248024222737/250000000000 : ℝ) (19841937819/20000000000 : ℝ) (124012111353/125000000000 : ℝ) (496048445413/500000000000 : ℝ) (496048445443/500000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 3 (496048445443/500000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 4 (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 5 (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 6 (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16673/131072 : ℝ)) 7 (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16673/131072 : ℝ))) (88460277361/500000000000 : ℝ) (176920554729/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88460277361/500000000000 : ℝ) (176920554729/1000000000000 : ℝ) (588460277361/1000000000000 : ℝ) (117692055473/200000000000 : ℝ) (420619251487/1000000000000 : ℝ) (52577406437/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 1 (588460277361/1000000000000 : ℝ) (117692055473/200000000000 : ℝ) (420619251487/1000000000000 : ℝ) (52577406437/125000000000 : ℝ) (63067470553/125000000000 : ℝ) (504539764431/1000000000000 : ℝ) (99502305781/200000000000 : ℝ) (497511528913/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 2 (63067470553/125000000000 : ℝ) (504539764431/1000000000000 : ℝ) (99502305781/200000000000 : ℝ) (497511528913/1000000000000 : ℝ) (62628205833/125000000000 : ℝ) (31314102917/62500000000 : ℝ) (31313332673/62500000000 : ℝ) (501013322777/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 3 (62628205833/125000000000 : ℝ) (31314102917/62500000000 : ℝ) (31313332673/62500000000 : ℝ) (501013322777/1000000000000 : ℝ) (125254871179/250000000000 : ℝ) (20040779389/40000000000 : ℝ) (250509742339/500000000000 : ℝ) (501019484687/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 4 (125254871179/250000000000 : ℝ) (20040779389/40000000000 : ℝ) (250509742339/500000000000 : ℝ) (501019484687/1000000000000 : ℝ) (501019484697/1000000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 5 (501019484697/1000000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 6 (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16673/131072 : ℝ))) 7 (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16673/131072 : ℝ)) hmem 8 (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16673/131072 : ℝ))) hcmem 8 (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16673/131072 : ℝ)) (198419378177/200000000000 : ℝ) (124012111361/125000000000 : ℝ) (62627435587/125000000000 : ℝ) (250509742353/500000000000 : ℝ) (793268856541/1000000000000 : ℝ) (9915860707/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0619_exp_lower
  have heNumeric : (64215708947/31250000000 : ℝ)/4 ≤ Real.exp (-17051286243561/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215708947/31250000000 : ℝ)/4 ≤ Real.exp ((66691/524288 : ℝ)-(9915860707/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66691/524288 : ℝ) (16673/131072 : ℝ) (9915860707/12500000000 : ℝ) (64215708947/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0620; no trusted numerical premise.
theorem cover8_leaf0620_exp_radius : (124751795961790543/125000000000000000 : ℝ) ≤ Real.exp ((-66693/4194304 : ℝ)/8) ∧ Real.exp ((-66693/4194304 : ℝ)/8) ≤ (199602873538864869/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66693/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0620_exp_lower : (57507094485496989/62500000000000000 : ℝ) ≤ Real.exp ((-21314107953551/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314107953551/32000000000000 : ℝ)/8) ≤ (36804540470718073/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314107953551/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0620_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490267673/100000000000 : ℝ) ≤ 4*Real.exp (16673/131072 : ℝ)*Real.exp (-mu (radius 8 (66693/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490267673/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66693/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0620_exp_radius
  have hrNumeric : (39368996033/40000000000 : ℝ) ≤ Real.exp (-66693/4194304 : ℝ) ∧ Real.exp (-66693/4194304 : ℝ) ≤ (492112450413/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39368996033/40000000000 : ℝ) ≤ (radius 8 (66693/524288 : ℝ)) ∧ (radius 8 (66693/524288 : ℝ)) ≤ (492112450413/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66693/524288 : ℝ)) (39368996033/40000000000 : ℝ) (492112450413/500000000000 : ℝ) (22115232517/125000000000 : ℝ) (88460930071/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66693/524288 : ℝ)) (39368996033/40000000000 : ℝ) (492112450413/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39368996033/40000000000 : ℝ) (492112450413/500000000000 : ℝ) (248028112603/250000000000 : ℝ) (992112450413/1000000000000 : ℝ) (992081095891/1000000000000 : ℝ) (248020273973/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 1 (248028112603/250000000000 : ℝ) (992112450413/1000000000000 : ℝ) (992081095891/1000000000000 : ℝ) (248020273973/250000000000 : ℝ) (992096773151/1000000000000 : ℝ) (992096773153/1000000000000 : ℝ) (992096773027/1000000000000 : ℝ) (992096773029/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 2 (992096773151/1000000000000 : ℝ) (992096773153/1000000000000 : ℝ) (992096773027/1000000000000 : ℝ) (992096773029/1000000000000 : ℝ) (992096773089/1000000000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 3 (992096773089/1000000000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 4 (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 5 (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 6 (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66693/524288 : ℝ)) 7 (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66693/524288 : ℝ))) (22115232517/125000000000 : ℝ) (88460930071/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22115232517/125000000000 : ℝ) (88460930071/500000000000 : ℝ) (147115232517/250000000000 : ℝ) (588460930071/1000000000000 : ℝ) (420620803261/1000000000000 : ℝ) (420620803269/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 1 (147115232517/250000000000 : ℝ) (588460930071/1000000000000 : ℝ) (420620803261/1000000000000 : ℝ) (420620803269/1000000000000 : ℝ) (63067608333/125000000000 : ℝ) (50454086667/100000000000 : ℝ) (497512722543/1000000000000 : ℝ) (9950254451/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 2 (63067608333/125000000000 : ℝ) (50454086667/100000000000 : ℝ) (497512722543/1000000000000 : ℝ) (9950254451/20000000000 : ℝ) (501026794603/1000000000000 : ℝ) (50102679461/100000000000 : ℝ) (31313404441/62500000000 : ℝ) (62626808883/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 3 (501026794603/1000000000000 : ℝ) (50102679461/100000000000 : ℝ) (31313404441/62500000000 : ℝ) (62626808883/125000000000 : ℝ) (501020632829/1000000000000 : ℝ) (501020632837/1000000000000 : ℝ) (501020632791/1000000000000 : ℝ) (626275791/1250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 4 (501020632829/1000000000000 : ℝ) (501020632837/1000000000000 : ℝ) (501020632791/1000000000000 : ℝ) (626275791/1250000000 : ℝ) (50102063281/100000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 5 (50102063281/100000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 6 (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66693/524288 : ℝ))) 7 (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66693/524288 : ℝ)) hmem 8 (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66693/524288 : ℝ))) hcmem 8 (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66693/524288 : ℝ)) (31003024159/31250000000 : ℝ) (992096773091/1000000000000 : ℝ) (501020632809/1000000000000 : ℝ) (501020632819/1000000000000 : ℝ) (198317692137/250000000000 : ℝ) (99158846071/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0620_exp_lower
  have heNumeric : (205490267673/100000000000 : ℝ)/4 ≤ Real.exp (-21314107953551/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490267673/100000000000 : ℝ)/4 ≤ Real.exp ((16673/131072 : ℝ)-(99158846071/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16673/131072 : ℝ) (66693/524288 : ℝ) (99158846071/125000000000 : ℝ) (205490267673/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0621; no trusted numerical premise.
theorem cover8_leaf0621_exp_radius : (499007168975589427/500000000000000000 : ℝ) ≤ Real.exp ((-33347/2097152 : ℝ)/8) ∧ Real.exp ((-33347/2097152 : ℝ)/8) ≤ (199602867590235771/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33347/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0621_exp_lower : (920113511233438657/1000000000000000000 : ℝ) ≤ Real.exp ((-85256432409067/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256432409067/128000000000000 : ℝ)/8) ≤ (460056755616719329/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256432409067/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0621_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745133359/50000000000 : ℝ) ≤ 4*Real.exp (66693/524288 : ℝ)*Real.exp (-mu (radius 8 (33347/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745133359/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33347/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0621_exp_radius
  have hrNumeric : (984224666167/1000000000000 : ℝ) ≤ Real.exp (-33347/2097152 : ℝ) ∧ Real.exp (-33347/2097152 : ℝ) ≤ (123028083271/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984224666167/1000000000000 : ℝ) ≤ (radius 8 (33347/262144 : ℝ)) ∧ (radius 8 (33347/262144 : ℝ)) ≤ (123028083271/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33347/262144 : ℝ)) (984224666167/1000000000000 : ℝ) (123028083271/125000000000 : ℝ) (35384633109/200000000000 : ℝ) (176923165551/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33347/262144 : ℝ)) (984224666167/1000000000000 : ℝ) (123028083271/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984224666167/1000000000000 : ℝ) (123028083271/125000000000 : ℝ) (992112333083/1000000000000 : ℝ) (248028083271/250000000000 : ℝ) (7936647821/8000000000 : ℝ) (992080977627/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 1 (992112333083/1000000000000 : ℝ) (248028083271/250000000000 : ℝ) (7936647821/8000000000 : ℝ) (992080977627/1000000000000 : ℝ) (496048327677/500000000000 : ℝ) (248024163839/250000000000 : ℝ) (99209665523/100000000000 : ℝ) (7750755119/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 2 (496048327677/500000000000 : ℝ) (248024163839/250000000000 : ℝ) (99209665523/100000000000 : ℝ) (7750755119/7812500000 : ℝ) (248024163823/250000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 3 (248024163823/250000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 4 (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 5 (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 6 (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33347/262144 : ℝ)) 7 (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33347/262144 : ℝ))) (35384633109/200000000000 : ℝ) (176923165551/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35384633109/200000000000 : ℝ) (176923165551/1000000000000 : ℝ) (147115395693/250000000000 : ℝ) (73557697847/125000000000 : ℝ) (210311177511/500000000000 : ℝ) (420622355031/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 1 (147115395693/250000000000 : ℝ) (73557697847/125000000000 : ℝ) (210311177511/500000000000 : ℝ) (420622355031/1000000000000 : ℝ) (504541968897/1000000000000 : ℝ) (63067746113/125000000000 : ℝ) (124378479043/250000000000 : ℝ) (24875695809/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 2 (504541968897/1000000000000 : ℝ) (63067746113/125000000000 : ℝ) (124378479043/250000000000 : ℝ) (24875695809/50000000000 : ℝ) (250513971267/500000000000 : ℝ) (250513971271/500000000000 : ℝ) (62626952417/125000000000 : ℝ) (31313476209/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 3 (250513971267/500000000000 : ℝ) (250513971271/500000000000 : ℝ) (62626952417/125000000000 : ℝ) (31313476209/62500000000 : ℝ) (100204356187/200000000000 : ℝ) (501021780943/1000000000000 : ℝ) (501021780897/1000000000000 : ℝ) (250510890453/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 4 (100204356187/200000000000 : ℝ) (501021780943/1000000000000 : ℝ) (501021780897/1000000000000 : ℝ) (250510890453/500000000000 : ℝ) (125255445229/250000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 5 (125255445229/250000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 6 (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33347/262144 : ℝ))) 7 (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33347/262144 : ℝ)) hmem 8 (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33347/262144 : ℝ))) hcmem 8 (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33347/262144 : ℝ)) (992096655291/1000000000000 : ℝ) (496048327647/500000000000 : ℝ) (100204356183/200000000000 : ℝ) (20040871237/40000000000 : ℝ) (158654536109/200000000000 : ℝ) (198318170141/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0621_exp_lower
  have heNumeric : (102745133359/50000000000 : ℝ)/4 ≤ Real.exp (-85256432409067/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745133359/50000000000 : ℝ)/4 ≤ Real.exp ((66693/524288 : ℝ)-(198318170141/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66693/524288 : ℝ) (33347/262144 : ℝ) (198318170141/250000000000 : ℝ) (102745133359/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0622; no trusted numerical premise.
theorem cover8_leaf0622_exp_radius : (3992057232832137/4000000000000000 : ℝ) ≤ Real.exp ((-66695/4194304 : ℝ)/8) ∧ Real.exp ((-66695/4194304 : ℝ)/8) ≤ (998014308208034251/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66695/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0622_exp_lower : (230028377675450211/250000000000000000 : ℝ) ≤ Real.exp ((-8525643300073/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525643300073/12800000000000 : ℝ)/8) ≤ (184022702140360169/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525643300073/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0622_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902657681/1000000000000 : ℝ) ≤ 4*Real.exp (33347/262144 : ℝ)*Real.exp (-mu (radius 8 (66695/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902657681/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66695/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0622_exp_radius
  have hrNumeric : (98422443151/100000000000 : ℝ) ≤ Real.exp (-66695/4194304 : ℝ) ∧ Real.exp (-66695/4194304 : ℝ) ≤ (984224431511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98422443151/100000000000 : ℝ) ≤ (radius 8 (66695/524288 : ℝ)) ∧ (radius 8 (66695/524288 : ℝ)) ≤ (984224431511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66695/524288 : ℝ)) (98422443151/100000000000 : ℝ) (984224431511/1000000000000 : ℝ) (88462235469/500000000000 : ℝ) (35384894189/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66695/524288 : ℝ)) (98422443151/100000000000 : ℝ) (984224431511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98422443151/100000000000 : ℝ) (984224431511/1000000000000 : ℝ) (198422443151/200000000000 : ℝ) (248028053939/250000000000 : ℝ) (6200505371/6250000000 : ℝ) (496040429681/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 1 (198422443151/200000000000 : ℝ) (248028053939/250000000000 : ℝ) (6200505371/6250000000 : ℝ) (496040429681/500000000000 : ℝ) (992096537557/1000000000000 : ℝ) (992096537559/1000000000000 : ℝ) (992096537433/1000000000000 : ℝ) (248024134359/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 2 (992096537557/1000000000000 : ℝ) (992096537559/1000000000000 : ℝ) (992096537433/1000000000000 : ℝ) (248024134359/250000000000 : ℝ) (198419307499/200000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 3 (198419307499/200000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 4 (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 5 (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 6 (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66695/524288 : ℝ)) 7 (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66695/524288 : ℝ))) (88462235469/500000000000 : ℝ) (35384894189/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88462235469/500000000000 : ℝ) (35384894189/200000000000 : ℝ) (588462235469/1000000000000 : ℝ) (588462235473/1000000000000 : ℝ) (420623906759/1000000000000 : ℝ) (420623906769/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 1 (588462235469/1000000000000 : ℝ) (588462235473/1000000000000 : ℝ) (420623906759/1000000000000 : ℝ) (420623906769/1000000000000 : ℝ) (252271535557/500000000000 : ℝ) (504543071121/1000000000000 : ℝ) (497515109783/1000000000000 : ℝ) (15547347181/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 2 (252271535557/500000000000 : ℝ) (504543071121/1000000000000 : ℝ) (497515109783/1000000000000 : ℝ) (15547347181/31250000000 : ℝ) (31314318153/62500000000 : ℝ) (501029090457/1000000000000 : ℝ) (501016767599/1000000000000 : ℝ) (62627095951/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 3 (31314318153/62500000000 : ℝ) (501029090457/1000000000000 : ℝ) (501016767599/1000000000000 : ℝ) (62627095951/125000000000 : ℝ) (501022929023/1000000000000 : ℝ) (501022929033/1000000000000 : ℝ) (100204585797/200000000000 : ℝ) (100204585799/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 4 (501022929023/1000000000000 : ℝ) (501022929033/1000000000000 : ℝ) (100204585797/200000000000 : ℝ) (100204585799/200000000000 : ℝ) (125255732251/250000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 5 (125255732251/250000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 6 (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66695/524288 : ℝ))) 7 (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66695/524288 : ℝ)) hmem 8 (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66695/524288 : ℝ))) hcmem 8 (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66695/524288 : ℝ)) (496048268747/500000000000 : ℝ) (496048268749/500000000000 : ℝ) (501022929003/1000000000000 : ℝ) (250511464507/500000000000 : ℝ) (793274592513/1000000000000 : ℝ) (158654918507/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0622_exp_lower
  have heNumeric : (2054902657681/1000000000000 : ℝ)/4 ≤ Real.exp (-8525643300073/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902657681/1000000000000 : ℝ)/4 ≤ Real.exp ((33347/262144 : ℝ)-(158654918507/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33347/262144 : ℝ) (66695/524288 : ℝ) (158654918507/200000000000 : ℝ) (2054902657681/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0623; no trusted numerical premise.
theorem cover8_leaf0623_exp_radius : (249503569616222633/250000000000000000 : ℝ) ≤ Real.exp ((-8337/524288 : ℝ)/8) ∧ Real.exp ((-8337/524288 : ℝ)/8) ≤ (998014278464890533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8337/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0623_exp_lower : (230028377542972061/250000000000000000 : ℝ) ≤ Real.exp ((-85256433590473/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256433590473/128000000000000 : ℝ)/8) ≤ (184022702034377649/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256433590473/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0623_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451324107/500000000000 : ℝ) ≤ 4*Real.exp (66695/524288 : ℝ)*Real.exp (-mu (radius 8 (8337/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451324107/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8337/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0623_exp_radius
  have hrNumeric : (246056049213/250000000000 : ℝ) ≤ Real.exp (-8337/524288 : ℝ) ∧ Real.exp (-8337/524288 : ℝ) ≤ (984224196853/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246056049213/250000000000 : ℝ) ≤ (radius 8 (8337/65536 : ℝ)) ∧ (radius 8 (8337/65536 : ℝ)) ≤ (984224196853/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8337/65536 : ℝ)) (246056049213/250000000000 : ℝ) (984224196853/1000000000000 : ℝ) (176925776327/1000000000000 : ℝ) (88462888167/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8337/65536 : ℝ)) (246056049213/250000000000 : ℝ) (984224196853/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246056049213/250000000000 : ℝ) (984224196853/1000000000000 : ℝ) (496056049213/500000000000 : ℝ) (992112098427/1000000000000 : ℝ) (198416148219/200000000000 : ℝ) (124010092637/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 1 (496056049213/500000000000 : ℝ) (992112098427/1000000000000 : ℝ) (198416148219/200000000000 : ℝ) (124010092637/125000000000 : ℝ) (12401205247/12500000000 : ℝ) (496048209881/500000000000 : ℝ) (248024104909/250000000000 : ℝ) (496048209819/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 2 (12401205247/12500000000 : ℝ) (496048209881/500000000000 : ℝ) (248024104909/250000000000 : ℝ) (496048209819/500000000000 : ℝ) (496048209849/500000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 3 (496048209849/500000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 4 (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 5 (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 6 (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8337/65536 : ℝ)) 7 (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8337/65536 : ℝ))) (176925776327/1000000000000 : ℝ) (88462888167/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176925776327/1000000000000 : ℝ) (88462888167/500000000000 : ℝ) (588462888163/1000000000000 : ℝ) (588462888167/1000000000000 : ℝ) (210312729243/500000000000 : ℝ) (84125091699/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 1 (588462888163/1000000000000 : ℝ) (588462888167/1000000000000 : ℝ) (210312729243/500000000000 : ℝ) (84125091699/200000000000 : ℝ) (126136043331/250000000000 : ℝ) (504544173331/1000000000000 : ℝ) (248758151693/500000000000 : ℝ) (248758151697/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 2 (126136043331/250000000000 : ℝ) (504544173331/1000000000000 : ℝ) (248758151693/500000000000 : ℝ) (248758151697/500000000000 : ℝ) (100206047671/200000000000 : ℝ) (501030238363/1000000000000 : ℝ) (250508957927/500000000000 : ℝ) (250508957931/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 3 (100206047671/200000000000 : ℝ) (501030238363/1000000000000 : ℝ) (250508957927/500000000000 : ℝ) (250508957931/500000000000 : ℝ) (31314004819/62500000000 : ℝ) (501024077113/1000000000000 : ℝ) (250512038533/500000000000 : ℝ) (20040963083/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 4 (31314004819/62500000000 : ℝ) (501024077113/1000000000000 : ℝ) (250512038533/500000000000 : ℝ) (20040963083/40000000000 : ℝ) (100204815417/200000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 5 (100204815417/200000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 6 (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8337/65536 : ℝ))) 7 (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8337/65536 : ℝ)) hmem 8 (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8337/65536 : ℝ))) hcmem 8 (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8337/65536 : ℝ)) (992096419697/1000000000000 : ℝ) (9920964197/10000000000 : ℝ) (125256019271/250000000000 : ℝ) (250512038547/500000000000 : ℝ) (99159563059/125000000000 : ℝ) (793276504491/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0623_exp_lower
  have heNumeric : (1027451324107/500000000000 : ℝ)/4 ≤ Real.exp (-85256433590473/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451324107/500000000000 : ℝ)/4 ≤ Real.exp ((66695/524288 : ℝ)-(793276504491/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66695/524288 : ℝ) (8337/65536 : ℝ) (793276504491/1000000000000 : ℝ) (1027451324107/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0624; no trusted numerical premise.
theorem cover8_leaf0624_exp_radius : (998014248721747701/1000000000000000000 : ℝ) ≤ Real.exp ((-66697/4194304 : ℝ)/8) ∧ Real.exp ((-66697/4194304 : ℝ)/8) ≤ (499007124360873851/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66697/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0624_exp_lower : (920113509644505957/1000000000000000000 : ℝ) ≤ Real.exp ((-426282170887/640000000000 : ℝ)/8) ∧ Real.exp ((-426282170887/640000000000 : ℝ)/8) ≤ (460056754822252979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426282170887/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0624_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902638791/1000000000000 : ℝ) ≤ 4*Real.exp (8337/65536 : ℝ)*Real.exp (-mu (radius 8 (66697/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902638791/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66697/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0624_exp_radius
  have hrNumeric : (196844792439/200000000000 : ℝ) ≤ Real.exp (-66697/4194304 : ℝ) ∧ Real.exp (-66697/4194304 : ℝ) ≤ (246055990549/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196844792439/200000000000 : ℝ) ≤ (radius 8 (66697/524288 : ℝ)) ∧ (radius 8 (66697/524288 : ℝ)) ≤ (246055990549/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66697/524288 : ℝ)) (196844792439/200000000000 : ℝ) (246055990549/250000000000 : ℝ) (1769270817/10000000000 : ℝ) (176927081707/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66697/524288 : ℝ)) (196844792439/200000000000 : ℝ) (246055990549/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196844792439/200000000000 : ℝ) (246055990549/250000000000 : ℝ) (992111981097/1000000000000 : ℝ) (496055990549/500000000000 : ℝ) (99208062283/100000000000 : ℝ) (992080622831/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 1 (992111981097/1000000000000 : ℝ) (496055990549/500000000000 : ℝ) (99208062283/100000000000 : ℝ) (992080622831/1000000000000 : ℝ) (992096301963/1000000000000 : ℝ) (198419260393/200000000000 : ℝ) (992096301839/1000000000000 : ℝ) (992096301841/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 2 (992096301963/1000000000000 : ℝ) (198419260393/200000000000 : ℝ) (992096301839/1000000000000 : ℝ) (992096301841/1000000000000 : ℝ) (992096301901/1000000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 3 (992096301901/1000000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 4 (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 5 (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 6 (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66697/524288 : ℝ)) 7 (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66697/524288 : ℝ))) (1769270817/10000000000 : ℝ) (176927081707/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1769270817/10000000000 : ℝ) (176927081707/1000000000000 : ℝ) (11769270817/20000000000 : ℝ) (294231770427/500000000000 : ℝ) (105156752547/250000000000 : ℝ) (420627010197/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 1 (11769270817/20000000000 : ℝ) (294231770427/500000000000 : ℝ) (105156752547/250000000000 : ℝ) (420627010197/1000000000000 : ℝ) (504545275519/1000000000000 : ℝ) (252272637763/500000000000 : ℝ) (497517496971/1000000000000 : ℝ) (497517496979/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 2 (504545275519/1000000000000 : ℝ) (252272637763/500000000000 : ℝ) (497517496971/1000000000000 : ℝ) (497517496979/1000000000000 : ℝ) (100206277249/200000000000 : ℝ) (501031386253/1000000000000 : ℝ) (501019064093/1000000000000 : ℝ) (501019064101/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 3 (100206277249/200000000000 : ℝ) (501031386253/1000000000000 : ℝ) (501019064093/1000000000000 : ℝ) (501019064101/1000000000000 : ℝ) (501025225169/1000000000000 : ℝ) (501025225177/1000000000000 : ℝ) (501025225131/1000000000000 : ℝ) (25051261257/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 4 (501025225169/1000000000000 : ℝ) (501025225177/1000000000000 : ℝ) (501025225131/1000000000000 : ℝ) (25051261257/50000000000 : ℝ) (10020504503/20000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 5 (10020504503/20000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 6 (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66697/524288 : ℝ))) 7 (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66697/524288 : ℝ)) hmem 8 (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66697/524288 : ℝ))) hcmem 8 (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66697/524288 : ℝ)) (9920963019/10000000000 : ℝ) (992096301903/1000000000000 : ℝ) (501025225149/1000000000000 : ℝ) (501025225159/1000000000000 : ℝ) (158655683281/200000000000 : ℝ) (31731136657/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0624_exp_lower
  have heNumeric : (2054902638791/1000000000000 : ℝ)/4 ≤ Real.exp (-426282170887/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902638791/1000000000000 : ℝ)/4 ≤ Real.exp ((8337/65536 : ℝ)-(31731136657/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8337/65536 : ℝ) (66697/524288 : ℝ) (31731136657/40000000000 : ℝ) (2054902638791/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0600_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0600_certificate
#check SmaleRate.Proofs.cover8_leaf0601_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0601_certificate
#check SmaleRate.Proofs.cover8_leaf0602_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0602_certificate
#check SmaleRate.Proofs.cover8_leaf0603_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0603_certificate
#check SmaleRate.Proofs.cover8_leaf0604_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0604_certificate
#check SmaleRate.Proofs.cover8_leaf0605_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0605_certificate
#check SmaleRate.Proofs.cover8_leaf0606_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0606_certificate
#check SmaleRate.Proofs.cover8_leaf0607_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0607_certificate
#check SmaleRate.Proofs.cover8_leaf0608_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0608_certificate
#check SmaleRate.Proofs.cover8_leaf0609_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0609_certificate
#check SmaleRate.Proofs.cover8_leaf0610_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0610_certificate
#check SmaleRate.Proofs.cover8_leaf0611_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0611_certificate
#check SmaleRate.Proofs.cover8_leaf0612_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0612_certificate
#check SmaleRate.Proofs.cover8_leaf0613_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0613_certificate
#check SmaleRate.Proofs.cover8_leaf0614_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0614_certificate
#check SmaleRate.Proofs.cover8_leaf0615_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0615_certificate
#check SmaleRate.Proofs.cover8_leaf0616_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0616_certificate
#check SmaleRate.Proofs.cover8_leaf0617_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0617_certificate
#check SmaleRate.Proofs.cover8_leaf0618_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0618_certificate
#check SmaleRate.Proofs.cover8_leaf0619_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0619_certificate
#check SmaleRate.Proofs.cover8_leaf0620_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0620_certificate
#check SmaleRate.Proofs.cover8_leaf0621_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0621_certificate
#check SmaleRate.Proofs.cover8_leaf0622_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0622_certificate
#check SmaleRate.Proofs.cover8_leaf0623_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0623_certificate
#check SmaleRate.Proofs.cover8_leaf0624_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0624_certificate
