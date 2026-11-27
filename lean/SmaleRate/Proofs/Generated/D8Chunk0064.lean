/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1600; no trusted numerical premise.
theorem cover8_leaf1600_exp_radius : (3118569324030369/3125000000000000 : ℝ) ≤ Real.exp ((-135/8192 : ℝ)/8) ∧ Real.exp ((-135/8192 : ℝ)/8) ≤ (997942183689718081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-135/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1600_exp_lower : (460057687343104949/500000000000000000 : ℝ) ≤ Real.exp ((-5328397410193/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328397410193/8000000000000 : ℝ)/8) ≤ (920115374686209899/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328397410193/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1600_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027467980411/500000000000 : ℝ) ≤ 4*Real.exp (4319/32768 : ℝ)*Real.exp (-mu (radius 8 (135/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (1027467980411/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (135/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1600_exp_radius
  have hrNumeric : (983655551807/1000000000000 : ℝ) ≤ Real.exp (-135/8192 : ℝ) ∧ Real.exp (-135/8192 : ℝ) ≤ (15369617997/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983655551807/1000000000000 : ℝ) ≤ (radius 8 (135/1024 : ℝ)) ∧ (radius 8 (135/1024 : ℝ)) ≤ (15369617997/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (135/1024 : ℝ)) (983655551807/1000000000000 : ℝ) (15369617997/15625000000 : ℝ) (90030210759/500000000000 : ℝ) (45015105381/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (135/1024 : ℝ)) (983655551807/1000000000000 : ℝ) (15369617997/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (135/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983655551807/1000000000000 : ℝ) (15369617997/15625000000 : ℝ) (991827775903/1000000000000 : ℝ) (30994617997/31250000000 : ℝ) (61987131723/62500000000 : ℝ) (991794107569/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (135/1024 : ℝ)) 1 (991827775903/1000000000000 : ℝ) (30994617997/31250000000 : ℝ) (61987131723/62500000000 : ℝ) (991794107569/1000000000000 : ℝ) (198362188347/200000000000 : ℝ) (991810941737/1000000000000 : ℝ) (123976367699/125000000000 : ℝ) (495905470797/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (135/1024 : ℝ)) 2 (198362188347/200000000000 : ℝ) (991810941737/1000000000000 : ℝ) (123976367699/125000000000 : ℝ) (495905470797/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (135/1024 : ℝ)) 3 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (135/1024 : ℝ)) 4 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (135/1024 : ℝ)) 5 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (135/1024 : ℝ)) 6 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (135/1024 : ℝ)) 7 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (135/1024 : ℝ))) (90030210759/500000000000 : ℝ) (45015105381/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90030210759/500000000000 : ℝ) (45015105381/250000000000 : ℝ) (590030210759/1000000000000 : ℝ) (295015105381/500000000000 : ℝ) (424335270179/1000000000000 : ℝ) (424335270187/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 1 (590030210759/1000000000000 : ℝ) (295015105381/500000000000 : ℝ) (424335270179/1000000000000 : ℝ) (424335270187/1000000000000 : ℝ) (507182740469/1000000000000 : ℝ) (20287309619/40000000000 : ℝ) (31273155727/62500000000 : ℝ) (500370491639/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 2 (507182740469/1000000000000 : ℝ) (20287309619/40000000000 : ℝ) (31273155727/62500000000 : ℝ) (500370491639/1000000000000 : ℝ) (10075532321/20000000000 : ℝ) (503776616057/1000000000000 : ℝ) (62970637651/125000000000 : ℝ) (15742659413/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 3 (10075532321/20000000000 : ℝ) (503776616057/1000000000000 : ℝ) (62970637651/125000000000 : ℝ) (15742659413/31250000000 : ℝ) (503770858629/1000000000000 : ℝ) (503770858637/1000000000000 : ℝ) (125942714649/250000000000 : ℝ) (125942714651/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 4 (503770858629/1000000000000 : ℝ) (503770858637/1000000000000 : ℝ) (125942714649/250000000000 : ℝ) (125942714651/250000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 5 (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 6 (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (135/1024 : ℝ))) 7 (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (135/1024 : ℝ)) hmem 8 (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (135/1024 : ℝ))) hcmem 8 (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (135/1024 : ℝ)) (991810941663/1000000000000 : ℝ) (495905470833/500000000000 : ℝ) (125942714653/250000000000 : ℝ) (503770858621/1000000000000 : ℝ) (398927548089/500000000000 : ℝ) (199463774049/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1600_exp_lower
  have heNumeric : (1027467980411/500000000000 : ℝ)/4 ≤ Real.exp (-5328397410193/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027467980411/500000000000 : ℝ)/4 ≤ Real.exp ((4319/32768 : ℝ)-(199463774049/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4319/32768 : ℝ) (135/1024 : ℝ) (199463774049/250000000000 : ℝ) (1027467980411/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1601; no trusted numerical premise.
theorem cover8_leaf1601_exp_radius : (997941707833916611/1000000000000000000 : ℝ) ≤ Real.exp ((-4321/262144 : ℝ)/8) ∧ Real.exp ((-4321/262144 : ℝ)/8) ≤ (249485426958479153/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4321/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1601_exp_lower : (920115450587579793/1000000000000000000 : ℝ) ≤ Real.exp ((-133209803269/200000000000 : ℝ)/8) ∧ Real.exp ((-133209803269/200000000000 : ℝ)/8) ≤ (460057725293789897/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133209803269/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1601_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027468658467/500000000000 : ℝ) ≤ 4*Real.exp (135/1024 : ℝ)*Real.exp (-mu (radius 8 (4321/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027468658467/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4321/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1601_exp_radius
  have hrNumeric : (491825899733/500000000000 : ℝ) ≤ Real.exp (-4321/262144 : ℝ) ∧ Real.exp (-4321/262144 : ℝ) ≤ (983651799467/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491825899733/500000000000 : ℝ) ≤ (radius 8 (4321/32768 : ℝ)) ∧ (radius 8 (4321/32768 : ℝ)) ≤ (983651799467/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4321/32768 : ℝ)) (491825899733/500000000000 : ℝ) (983651799467/1000000000000 : ℝ) (22510114881/125000000000 : ℝ) (90040459527/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4321/32768 : ℝ)) (491825899733/500000000000 : ℝ) (983651799467/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491825899733/500000000000 : ℝ) (983651799467/1000000000000 : ℝ) (991825899733/1000000000000 : ℝ) (495912949867/500000000000 : ℝ) (15496753373/15625000000 : ℝ) (495896107937/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 1 (991825899733/1000000000000 : ℝ) (495912949867/500000000000 : ℝ) (15496753373/15625000000 : ℝ) (495896107937/500000000000 : ℝ) (495904528901/500000000000 : ℝ) (247952264451/250000000000 : ℝ) (991809057659/1000000000000 : ℝ) (495904528831/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 2 (495904528901/500000000000 : ℝ) (247952264451/250000000000 : ℝ) (991809057659/1000000000000 : ℝ) (495904528831/500000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 3 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 4 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 5 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 6 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4321/32768 : ℝ)) 7 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4321/32768 : ℝ))) (22510114881/125000000000 : ℝ) (90040459527/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22510114881/125000000000 : ℝ) (90040459527/500000000000 : ℝ) (147510114881/250000000000 : ℝ) (590040459527/1000000000000 : ℝ) (424359422009/1000000000000 : ℝ) (424359422017/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 1 (147510114881/250000000000 : ℝ) (590040459527/1000000000000 : ℝ) (424359422009/1000000000000 : ℝ) (424359422017/1000000000000 : ℝ) (253599970383/500000000000 : ℝ) (126799985193/250000000000 : ℝ) (62548634623/125000000000 : ℝ) (500389076991/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 2 (253599970383/500000000000 : ℝ) (126799985193/250000000000 : ℝ) (62548634623/125000000000 : ℝ) (500389076991/1000000000000 : ℝ) (4030356071/8000000000 : ℝ) (251897254441/500000000000 : ℝ) (503782999123/1000000000000 : ℝ) (503782999131/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 3 (4030356071/8000000000 : ℝ) (251897254441/500000000000 : ℝ) (503782999123/1000000000000 : ℝ) (503782999131/1000000000000 : ℝ) (503788753999/1000000000000 : ℝ) (503788754007/1000000000000 : ℝ) (251894376983/500000000000 : ℝ) (251894376987/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 4 (503788753999/1000000000000 : ℝ) (503788754007/1000000000000 : ℝ) (251894376983/500000000000 : ℝ) (251894376987/500000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 5 (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 6 (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4321/32768 : ℝ))) 7 (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4321/32768 : ℝ)) hmem 8 (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4321/32768 : ℝ))) hcmem 8 (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4321/32768 : ℝ)) (99180905773/100000000000 : ℝ) (991809057733/1000000000000 : ℝ) (251894376991/500000000000 : ℝ) (503788753991/1000000000000 : ℝ) (199471238457/250000000000 : ℝ) (159576990769/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1601_exp_lower
  have heNumeric : (1027468658467/500000000000 : ℝ)/4 ≤ Real.exp (-133209803269/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027468658467/500000000000 : ℝ)/4 ≤ Real.exp ((135/1024 : ℝ)-(159576990769/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (135/1024 : ℝ) (4321/32768 : ℝ) (159576990769/200000000000 : ℝ) (1027468658467/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1602; no trusted numerical premise.
theorem cover8_leaf1602_exp_radius : (31185663499323189/31250000000000000 : ℝ) ≤ Real.exp ((-2161/131072 : ℝ)/8) ∧ Real.exp ((-2161/131072 : ℝ)/8) ≤ (997941231978342049/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2161/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1602_exp_lower : (230028881756518347/250000000000000000 : ℝ) ≤ Real.exp ((-5328386813967/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328386813967/8000000000000 : ℝ)/8) ≤ (920115527026073389/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328386813967/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1602_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513734670661/250000000000 : ℝ) ≤ 4*Real.exp (4321/32768 : ℝ)*Real.exp (-mu (radius 8 (2161/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513734670661/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2161/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1602_exp_radius
  have hrNumeric : (983648047139/1000000000000 : ℝ) ≤ Real.exp (-2161/131072 : ℝ) ∧ Real.exp (-2161/131072 : ℝ) ≤ (49182402357/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983648047139/1000000000000 : ℝ) ≤ (radius 8 (2161/16384 : ℝ)) ∧ (radius 8 (2161/16384 : ℝ)) ≤ (49182402357/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2161/16384 : ℝ)) (983648047139/1000000000000 : ℝ) (49182402357/50000000000 : ℝ) (180101414091/1000000000000 : ℝ) (180101414097/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2161/16384 : ℝ)) (983648047139/1000000000000 : ℝ) (49182402357/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983648047139/1000000000000 : ℝ) (49182402357/50000000000 : ℝ) (991824023569/1000000000000 : ℝ) (99182402357/100000000000 : ℝ) (49589516209/50000000000 : ℝ) (495895162091/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 1 (991824023569/1000000000000 : ℝ) (99182402357/100000000000 : ℝ) (49589516209/50000000000 : ℝ) (495895162091/500000000000 : ℝ) (495903586937/500000000000 : ℝ) (247951793469/250000000000 : ℝ) (991807173731/1000000000000 : ℝ) (991807173733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 2 (495903586937/500000000000 : ℝ) (247951793469/250000000000 : ℝ) (991807173731/1000000000000 : ℝ) (991807173733/1000000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 3 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 4 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 5 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 6 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2161/16384 : ℝ)) 7 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2161/16384 : ℝ))) (180101414091/1000000000000 : ℝ) (180101414097/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180101414091/1000000000000 : ℝ) (180101414097/1000000000000 : ℝ) (118010141409/200000000000 : ℝ) (590050707049/1000000000000 : ℝ) (212191784767/500000000000 : ℝ) (212191784771/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 1 (118010141409/200000000000 : ℝ) (590050707049/1000000000000 : ℝ) (212191784767/500000000000 : ℝ) (212191784771/500000000000 : ℝ) (507217138289/1000000000000 : ℝ) (63402142287/125000000000 : ℝ) (20016306363/40000000000 : ℝ) (500407659083/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 2 (507217138289/1000000000000 : ℝ) (63402142287/125000000000 : ℝ) (20016306363/40000000000 : ℝ) (500407659083/1000000000000 : ℝ) (251906199341/500000000000 : ℝ) (50381239869/100000000000 : ℝ) (251900447009/500000000000 : ℝ) (503800894027/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 3 (251906199341/500000000000 : ℝ) (50381239869/100000000000 : ℝ) (251900447009/500000000000 : ℝ) (503800894027/1000000000000 : ℝ) (10076132927/20000000000 : ℝ) (503806646359/1000000000000 : ℝ) (503806646317/1000000000000 : ℝ) (251903323163/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 4 (10076132927/20000000000 : ℝ) (503806646359/1000000000000 : ℝ) (503806646317/1000000000000 : ℝ) (251903323163/500000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 5 (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 6 (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2161/16384 : ℝ))) 7 (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2161/16384 : ℝ)) hmem 8 (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2161/16384 : ℝ))) hcmem 8 (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2161/16384 : ℝ)) (495903586901/500000000000 : ℝ) (198361434761/200000000000 : ℝ) (503806646333/1000000000000 : ℝ) (503806646343/1000000000000 : ℝ) (159582961361/200000000000 : ℝ) (99739350853/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1602_exp_lower
  have heNumeric : (513734670661/250000000000 : ℝ)/4 ≤ Real.exp (-5328386813967/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513734670661/250000000000 : ℝ)/4 ≤ Real.exp ((4321/32768 : ℝ)-(99739350853/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4321/32768 : ℝ) (2161/16384 : ℝ) (99739350853/125000000000 : ℝ) (513734670661/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1603; no trusted numerical premise.
theorem cover8_leaf1603_exp_radius : (997940756122994391/1000000000000000000 : ℝ) ≤ Real.exp ((-4323/262144 : ℝ)/8) ∧ Real.exp ((-4323/262144 : ℝ)/8) ≤ (124742594515374299/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4323/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1603_exp_lower : (115014450500369497/125000000000000000 : ℝ) ≤ Real.exp ((-2664190729863/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664190729863/4000000000000 : ℝ)/8) ≤ (920115604002955977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664190729863/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1603_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027470028987/500000000000 : ℝ) ≤ 4*Real.exp (2161/16384 : ℝ)*Real.exp (-mu (radius 8 (4323/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027470028987/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4323/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1603_exp_radius
  have hrNumeric : (983644294827/1000000000000 : ℝ) ≤ Real.exp (-4323/262144 : ℝ) ∧ Real.exp (-4323/262144 : ℝ) ≤ (245911073707/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983644294827/1000000000000 : ℝ) ≤ (radius 8 (4323/32768 : ℝ)) ∧ (radius 8 (4323/32768 : ℝ)) ≤ (245911073707/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4323/32768 : ℝ)) (983644294827/1000000000000 : ℝ) (245911073707/250000000000 : ℝ) (180121906641/1000000000000 : ℝ) (22515238331/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4323/32768 : ℝ)) (983644294827/1000000000000 : ℝ) (245911073707/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983644294827/1000000000000 : ℝ) (245911073707/250000000000 : ℝ) (991822147413/1000000000000 : ℝ) (495911073707/500000000000 : ℝ) (991788432493/1000000000000 : ℝ) (495894216247/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 1 (991822147413/1000000000000 : ℝ) (495911073707/500000000000 : ℝ) (991788432493/1000000000000 : ℝ) (495894216247/500000000000 : ℝ) (991805289953/1000000000000 : ℝ) (495902644977/500000000000 : ℝ) (991805289809/1000000000000 : ℝ) (991805289811/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 2 (991805289953/1000000000000 : ℝ) (495902644977/500000000000 : ℝ) (991805289809/1000000000000 : ℝ) (991805289811/1000000000000 : ℝ) (991805289881/1000000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 3 (991805289881/1000000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 4 (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 5 (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 6 (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4323/32768 : ℝ)) 7 (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4323/32768 : ℝ))) (180121906641/1000000000000 : ℝ) (22515238331/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180121906641/1000000000000 : ℝ) (22515238331/125000000000 : ℝ) (14751523833/25000000000 : ℝ) (147515238331/250000000000 : ℝ) (424407712749/1000000000000 : ℝ) (212203856379/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 1 (14751523833/25000000000 : ℝ) (147515238331/250000000000 : ℝ) (424407712749/1000000000000 : ℝ) (212203856379/500000000000 : ℝ) (253617166517/500000000000 : ℝ) (507234333041/1000000000000 : ℝ) (250213118951/500000000000 : ℝ) (50042623791/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 2 (253617166517/500000000000 : ℝ) (507234333041/1000000000000 : ℝ) (250213118951/500000000000 : ℝ) (50042623791/100000000000 : ℝ) (125957571367/250000000000 : ℝ) (125957571369/250000000000 : ℝ) (503818785889/1000000000000 : ℝ) (503818785897/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 3 (125957571367/250000000000 : ℝ) (125957571369/250000000000 : ℝ) (503818785889/1000000000000 : ℝ) (503818785897/1000000000000 : ℝ) (251912267839/500000000000 : ℝ) (503824535687/1000000000000 : ℝ) (100764907129/200000000000 : ℝ) (251912267827/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 4 (251912267839/500000000000 : ℝ) (503824535687/1000000000000 : ℝ) (100764907129/200000000000 : ℝ) (251912267827/500000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 5 (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 6 (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4323/32768 : ℝ))) 7 (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4323/32768 : ℝ)) hmem 8 (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4323/32768 : ℝ))) hcmem 8 (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4323/32768 : ℝ)) (24795132247/25000000000 : ℝ) (991805289883/1000000000000 : ℝ) (503824535661/1000000000000 : ℝ) (503824535671/1000000000000 : ℝ) (797944655103/1000000000000 : ℝ) (398972327561/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1603_exp_lower
  have heNumeric : (1027470028987/500000000000 : ℝ)/4 ≤ Real.exp (-2664190729863/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027470028987/500000000000 : ℝ)/4 ≤ Real.exp ((2161/16384 : ℝ)-(398972327561/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2161/16384 : ℝ) (4323/32768 : ℝ) (398972327561/500000000000 : ℝ) (1027470028987/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1604; no trusted numerical premise.
theorem cover8_leaf1604_exp_radius : (997940280267873639/1000000000000000000 : ℝ) ≤ Real.exp ((-1081/65536 : ℝ)/8) ∧ Real.exp ((-1081/65536 : ℝ)/8) ≤ (24948507006696841/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1081/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1604_exp_lower : (920115681516617489/1000000000000000000 : ℝ) ≤ Real.exp ((-5328376068149/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328376068149/8000000000000 : ℝ)/8) ≤ (92011568151661749/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328376068149/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1604_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128433840181/62500000000 : ℝ) ≤ 4*Real.exp (4323/32768 : ℝ)*Real.exp (-mu (radius 8 (1081/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (128433840181/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1081/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1604_exp_radius
  have hrNumeric : (983640542529/1000000000000 : ℝ) ≤ Real.exp (-1081/65536 : ℝ) ∧ Real.exp (-1081/65536 : ℝ) ≤ (98364054253/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983640542529/1000000000000 : ℝ) ≤ (radius 8 (1081/8192 : ℝ)) ∧ (radius 8 (1081/8192 : ℝ)) ≤ (98364054253/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1081/8192 : ℝ)) (983640542529/1000000000000 : ℝ) (98364054253/100000000000 : ℝ) (90071198353/500000000000 : ℝ) (180142396713/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1081/8192 : ℝ)) (983640542529/1000000000000 : ℝ) (98364054253/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983640542529/1000000000000 : ℝ) (98364054253/100000000000 : ℝ) (30994383477/31250000000 : ℝ) (198364054253/200000000000 : ℝ) (123973317601/125000000000 : ℝ) (99178654081/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 1 (30994383477/31250000000 : ℝ) (198364054253/200000000000 : ℝ) (123973317601/125000000000 : ℝ) (99178654081/100000000000 : ℝ) (247950851509/250000000000 : ℝ) (495901703019/500000000000 : ℝ) (247950851473/250000000000 : ℝ) (198360681179/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 2 (247950851509/250000000000 : ℝ) (495901703019/500000000000 : ℝ) (247950851473/250000000000 : ℝ) (198360681179/200000000000 : ℝ) (247950851491/250000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 3 (247950851491/250000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 4 (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 5 (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 6 (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1081/8192 : ℝ)) 7 (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1081/8192 : ℝ))) (90071198353/500000000000 : ℝ) (180142396713/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90071198353/500000000000 : ℝ) (180142396713/1000000000000 : ℝ) (590071198353/1000000000000 : ℝ) (590071198357/1000000000000 : ℝ) (212215925831/500000000000 : ℝ) (53053981459/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 1 (590071198353/1000000000000 : ℝ) (590071198357/1000000000000 : ℝ) (212215925831/500000000000 : ℝ) (53053981459/125000000000 : ℝ) (507251525007/1000000000000 : ℝ) (101450305003/200000000000 : ℝ) (50044481347/100000000000 : ℝ) (250222406739/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 2 (507251525007/1000000000000 : ℝ) (101450305003/200000000000 : ℝ) (50044481347/100000000000 : ℝ) (250222406739/500000000000 : ℝ) (251924084619/500000000000 : ℝ) (503848169247/1000000000000 : ℝ) (503836674741/1000000000000 : ℝ) (2015346699/4000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 3 (251924084619/500000000000 : ℝ) (503848169247/1000000000000 : ℝ) (503836674741/1000000000000 : ℝ) (2015346699/4000000000 : ℝ) (503842421989/1000000000000 : ℝ) (503842421999/1000000000000 : ℝ) (125960605489/250000000000 : ℝ) (251921210983/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 4 (503842421989/1000000000000 : ℝ) (503842421999/1000000000000 : ℝ) (125960605489/250000000000 : ℝ) (251921210983/500000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 5 (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 6 (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1081/8192 : ℝ))) 7 (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1081/8192 : ℝ)) hmem 8 (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1081/8192 : ℝ))) hcmem 8 (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1081/8192 : ℝ)) (991803405963/1000000000000 : ℝ) (991803405967/1000000000000 : ℝ) (125960605493/250000000000 : ℝ) (503842421983/1000000000000 : ℝ) (797974498731/1000000000000 : ℝ) (797974498753/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1604_exp_lower
  have heNumeric : (128433840181/62500000000 : ℝ)/4 ≤ Real.exp (-5328376068149/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128433840181/62500000000 : ℝ)/4 ≤ Real.exp ((4323/32768 : ℝ)-(797974498753/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4323/32768 : ℝ) (1081/8192 : ℝ) (797974498753/1000000000000 : ℝ) (128433840181/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1605; no trusted numerical premise.
theorem cover8_leaf1605_exp_radius : (62371237775811237/62500000000000000 : ℝ) ≤ Real.exp ((-4325/262144 : ℝ)/8) ∧ Real.exp ((-4325/262144 : ℝ)/8) ≤ (997939804412979793/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4325/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1605_exp_lower : (230028939891822023/250000000000000000 : ℝ) ≤ Real.exp ((-266418531961/400000000000 : ℝ)/8) ∧ Real.exp ((-266418531961/400000000000 : ℝ)/8) ≤ (920115759567288093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266418531961/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1605_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054942837413/1000000000000 : ℝ) ≤ 4*Real.exp (1081/8192 : ℝ)*Real.exp (-mu (radius 8 (4325/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054942837413/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4325/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1605_exp_radius
  have hrNumeric : (196727358049/200000000000 : ℝ) ≤ Real.exp (-4325/262144 : ℝ) ∧ Real.exp (-4325/262144 : ℝ) ≤ (491818395123/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196727358049/200000000000 : ℝ) ≤ (radius 8 (4325/32768 : ℝ)) ∧ (radius 8 (4325/32768 : ℝ)) ≤ (491818395123/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4325/32768 : ℝ)) (196727358049/200000000000 : ℝ) (491818395123/500000000000 : ℝ) (90081442143/500000000000 : ℝ) (180162884293/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4325/32768 : ℝ)) (196727358049/200000000000 : ℝ) (491818395123/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196727358049/200000000000 : ℝ) (491818395123/500000000000 : ℝ) (495909197561/500000000000 : ℝ) (991818395123/1000000000000 : ℝ) (991784649127/1000000000000 : ℝ) (991784649129/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 1 (495909197561/500000000000 : ℝ) (991818395123/1000000000000 : ℝ) (991784649127/1000000000000 : ℝ) (991784649129/1000000000000 : ℝ) (247950380531/250000000000 : ℝ) (495900761063/500000000000 : ℝ) (49590076099/50000000000 : ℝ) (991801521983/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 2 (247950380531/250000000000 : ℝ) (495900761063/500000000000 : ℝ) (49590076099/50000000000 : ℝ) (991801521983/1000000000000 : ℝ) (247950380513/250000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 3 (247950380513/250000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 4 (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 5 (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 6 (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4325/32768 : ℝ)) 7 (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4325/32768 : ℝ))) (90081442143/500000000000 : ℝ) (180162884293/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90081442143/500000000000 : ℝ) (180162884293/1000000000000 : ℝ) (590081442143/1000000000000 : ℝ) (590081442147/1000000000000 : ℝ) (106113996569/250000000000 : ℝ) (84891197257/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 1 (590081442143/1000000000000 : ℝ) (590081442147/1000000000000 : ℝ) (106113996569/250000000000 : ℝ) (84891197257/200000000000 : ℝ) (507268714209/1000000000000 : ℝ) (63408589277/125000000000 : ℝ) (500463385781/1000000000000 : ℝ) (500463385789/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 2 (507268714209/1000000000000 : ℝ) (63408589277/125000000000 : ℝ) (500463385781/1000000000000 : ℝ) (500463385789/1000000000000 : ℝ) (100773209999/200000000000 : ℝ) (503866050003/1000000000000 : ℝ) (7872727509/15625000000 : ℝ) (100770912117/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 3 (100773209999/200000000000 : ℝ) (503866050003/1000000000000 : ℝ) (7872727509/15625000000 : ℝ) (100770912117/200000000000 : ℝ) (100772061057/200000000000 : ℝ) (251930152647/500000000000 : ℝ) (125965076313/250000000000 : ℝ) (251930152631/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 4 (100772061057/200000000000 : ℝ) (251930152647/500000000000 : ℝ) (125965076313/250000000000 : ℝ) (251930152631/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 5 (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 6 (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4325/32768 : ℝ))) 7 (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4325/32768 : ℝ)) hmem 8 (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4325/32768 : ℝ))) hcmem 8 (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4325/32768 : ℝ)) (991801522051/1000000000000 : ℝ) (198360304411/200000000000 : ℝ) (125965076317/250000000000 : ℝ) (251930152639/500000000000 : ℝ) (159600867539/200000000000 : ℝ) (159600867543/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1605_exp_lower
  have heNumeric : (2054942837413/1000000000000 : ℝ)/4 ≤ Real.exp (-266418531961/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054942837413/1000000000000 : ℝ)/4 ≤ Real.exp ((1081/8192 : ℝ)-(159600867543/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1081/8192 : ℝ) (4325/32768 : ℝ) (159600867543/200000000000 : ℝ) (2054942837413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1606; no trusted numerical premise.
theorem cover8_leaf1606_exp_radius : (997939328558312851/1000000000000000000 : ℝ) ≤ Real.exp ((-2163/131072 : ℝ)/8) ∧ Real.exp ((-2163/131072 : ℝ)/8) ≤ (249484832139578213/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2163/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1606_exp_lower : (184023167631108599/200000000000000000 : ℝ) ≤ Real.exp ((-5328365172899/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328365172899/8000000000000 : ℝ)/8) ≤ (230028959538885749/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328365172899/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1606_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410988848307/200000000000 : ℝ) ≤ 4*Real.exp (4325/32768 : ℝ)*Real.exp (-mu (radius 8 (2163/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410988848307/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2163/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1606_exp_radius
  have hrNumeric : (122954129747/125000000000 : ℝ) ≤ Real.exp (-2163/131072 : ℝ) ∧ Real.exp (-2163/131072 : ℝ) ≤ (983633037977/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122954129747/125000000000 : ℝ) ≤ (radius 8 (2163/16384 : ℝ)) ∧ (radius 8 (2163/16384 : ℝ)) ≤ (983633037977/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2163/16384 : ℝ)) (122954129747/125000000000 : ℝ) (983633037977/1000000000000 : ℝ) (180183369377/1000000000000 : ℝ) (180183369383/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2163/16384 : ℝ)) (122954129747/125000000000 : ℝ) (983633037977/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122954129747/125000000000 : ℝ) (983633037977/1000000000000 : ℝ) (247954129747/250000000000 : ℝ) (991816518989/1000000000000 : ℝ) (19835655149/20000000000 : ℝ) (991782757451/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 1 (247954129747/250000000000 : ℝ) (991816518989/1000000000000 : ℝ) (19835655149/20000000000 : ℝ) (991782757451/1000000000000 : ℝ) (991799638219/1000000000000 : ℝ) (49589981911/50000000000 : ℝ) (39671985523/40000000000 : ℝ) (991799638077/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 2 (991799638219/1000000000000 : ℝ) (49589981911/50000000000 : ℝ) (39671985523/40000000000 : ℝ) (991799638077/1000000000000 : ℝ) (991799638147/1000000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 3 (991799638147/1000000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 4 (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 5 (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 6 (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2163/16384 : ℝ)) 7 (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2163/16384 : ℝ))) (180183369377/1000000000000 : ℝ) (180183369383/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180183369377/1000000000000 : ℝ) (180183369383/1000000000000 : ℝ) (36880730293/62500000000 : ℝ) (147522921173/250000000000 : ℝ) (212240058293/500000000000 : ℝ) (212240058297/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 1 (36880730293/62500000000 : ℝ) (147522921173/250000000000 : ℝ) (212240058293/500000000000 : ℝ) (212240058297/500000000000 : ℝ) (507285900637/1000000000000 : ℝ) (507285900643/1000000000000 : ℝ) (31280122177/62500000000 : ℝ) (500481954839/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 2 (507285900637/1000000000000 : ℝ) (507285900643/1000000000000 : ℝ) (31280122177/62500000000 : ℝ) (500481954839/1000000000000 : ℝ) (251941963867/500000000000 : ℝ) (503883927741/1000000000000 : ℝ) (503872443391/1000000000000 : ℝ) (503872443399/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 3 (251941963867/500000000000 : ℝ) (503883927741/1000000000000 : ℝ) (503872443391/1000000000000 : ℝ) (503872443399/1000000000000 : ℝ) (251939092781/500000000000 : ℝ) (50387818557/100000000000 : ℝ) (503878185529/1000000000000 : ℝ) (251939092769/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 4 (251939092781/500000000000 : ℝ) (50387818557/100000000000 : ℝ) (503878185529/1000000000000 : ℝ) (251939092769/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 5 (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 6 (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2163/16384 : ℝ))) 7 (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2163/16384 : ℝ)) hmem 8 (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2163/16384 : ℝ))) hcmem 8 (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2163/16384 : ℝ)) (495899819073/500000000000 : ℝ) (991799638149/1000000000000 : ℝ) (100775637109/200000000000 : ℝ) (251939092777/500000000000 : ℝ) (159606834397/200000000000 : ℝ) (798034172003/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1606_exp_lower
  have heNumeric : (410988848307/200000000000 : ℝ)/4 ≤ Real.exp (-5328365172899/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410988848307/200000000000 : ℝ)/4 ≤ Real.exp ((4325/32768 : ℝ)-(798034172003/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4325/32768 : ℝ) (2163/16384 : ℝ) (798034172003/1000000000000 : ℝ) (410988848307/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1607; no trusted numerical premise.
theorem cover8_leaf1607_exp_radius : (498969426351936407/500000000000000000 : ℝ) ≤ Real.exp ((-4327/262144 : ℝ)/8) ∧ Real.exp ((-4327/262144 : ℝ)/8) ≤ (199587770540774563/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4327/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1607_exp_lower : (11501448966000027/12500000000000000 : ℝ) ≤ Real.exp ((-2664179834641/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664179834641/4000000000000 : ℝ)/8) ≤ (920115917280002161/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664179834641/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1607_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054945655239/1000000000000 : ℝ) ≤ 4*Real.exp (2163/16384 : ℝ)*Real.exp (-mu (radius 8 (4327/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054945655239/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4327/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1607_exp_radius
  have hrNumeric : (983629285721/1000000000000 : ℝ) ≤ Real.exp (-4327/262144 : ℝ) ∧ Real.exp (-4327/262144 : ℝ) ≤ (491814642861/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983629285721/1000000000000 : ℝ) ≤ (radius 8 (4327/32768 : ℝ)) ∧ (radius 8 (4327/32768 : ℝ)) ≤ (491814642861/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4327/32768 : ℝ)) (983629285721/1000000000000 : ℝ) (491814642861/500000000000 : ℝ) (11262740749/62500000000 : ℝ) (18020385199/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4327/32768 : ℝ)) (983629285721/1000000000000 : ℝ) (491814642861/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983629285721/1000000000000 : ℝ) (491814642861/500000000000 : ℝ) (49590732143/50000000000 : ℝ) (991814642861/1000000000000 : ℝ) (61986304111/62500000000 : ℝ) (495890432889/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 1 (49590732143/50000000000 : ℝ) (991814642861/1000000000000 : ℝ) (61986304111/62500000000 : ℝ) (495890432889/500000000000 : ℝ) (495898877159/500000000000 : ℝ) (12397471929/12500000000 : ℝ) (495898877087/500000000000 : ℝ) (15496839909/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 2 (495898877159/500000000000 : ℝ) (12397471929/12500000000 : ℝ) (495898877087/500000000000 : ℝ) (15496839909/15625000000 : ℝ) (495898877123/500000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 3 (495898877123/500000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 4 (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 5 (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 6 (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4327/32768 : ℝ)) 7 (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4327/32768 : ℝ))) (11262740749/62500000000 : ℝ) (18020385199/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11262740749/62500000000 : ℝ) (18020385199/100000000000 : ℝ) (73762740749/125000000000 : ℝ) (118020385199/200000000000 : ℝ) (212252121299/500000000000 : ℝ) (212252121303/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 1 (73762740749/125000000000 : ℝ) (118020385199/200000000000 : ℝ) (212252121299/500000000000 : ℝ) (212252121303/500000000000 : ℝ) (101460616859/200000000000 : ℝ) (507303084301/1000000000000 : ℝ) (500500520627/1000000000000 : ℝ) (250250260317/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 2 (101460616859/200000000000 : ℝ) (507303084301/1000000000000 : ℝ) (500500520627/1000000000000 : ℝ) (250250260317/500000000000 : ℝ) (503901802461/1000000000000 : ℝ) (125975450617/250000000000 : ℝ) (50389032319/100000000000 : ℝ) (251945161599/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 3 (503901802461/1000000000000 : ℝ) (125975450617/250000000000 : ℝ) (50389032319/100000000000 : ℝ) (251945161599/500000000000 : ℝ) (20155842513/40000000000 : ℝ) (503896062833/1000000000000 : ℝ) (62987007849/125000000000 : ℝ) (503896062801/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 4 (20155842513/40000000000 : ℝ) (503896062833/1000000000000 : ℝ) (62987007849/125000000000 : ℝ) (503896062801/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 5 (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 6 (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4327/32768 : ℝ))) 7 (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4327/32768 : ℝ)) hmem 8 (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4327/32768 : ℝ))) hcmem 8 (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4327/32768 : ℝ)) (198359550849/200000000000 : ℝ) (123974719281/125000000000 : ℝ) (62987007851/125000000000 : ℝ) (503896062817/1000000000000 : ℝ) (199516000403/250000000000 : ℝ) (798064001629/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1607_exp_lower
  have heNumeric : (2054945655239/1000000000000 : ℝ)/4 ≤ Real.exp (-2664179834641/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054945655239/1000000000000 : ℝ)/4 ≤ Real.exp ((2163/16384 : ℝ)-(798064001629/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2163/16384 : ℝ) (4327/32768 : ℝ) (798064001629/1000000000000 : ℝ) (2054945655239/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1608; no trusted numerical premise.
theorem cover8_leaf1608_exp_radius : (997938376849659683/1000000000000000000 : ℝ) ≤ Real.exp ((-541/32768 : ℝ)/8) ∧ Real.exp ((-541/32768 : ℝ)/8) ≤ (249484594212414921/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-541/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1608_exp_lower : (115014499617568839/125000000000000000 : ℝ) ≤ Real.exp ((-5328354128377/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328354128377/8000000000000 : ℝ)/8) ≤ (920115996940550713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328354128377/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1608_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027473539261/500000000000 : ℝ) ≤ 4*Real.exp (4327/32768 : ℝ)*Real.exp (-mu (radius 8 (541/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027473539261/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (541/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1608_exp_radius
  have hrNumeric : (24590638337/25000000000 : ℝ) ≤ Real.exp (-541/32768 : ℝ) ∧ Real.exp (-541/32768 : ℝ) ≤ (983625533481/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24590638337/25000000000 : ℝ) ≤ (radius 8 (541/4096 : ℝ)) ∧ (radius 8 (541/4096 : ℝ)) ≤ (983625533481/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (541/4096 : ℝ)) (24590638337/25000000000 : ℝ) (983625533481/1000000000000 : ℝ) (180224332109/1000000000000 : ℝ) (36044866423/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (541/4096 : ℝ)) (24590638337/25000000000 : ℝ) (983625533481/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (541/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24590638337/25000000000 : ℝ) (983625533481/1000000000000 : ℝ) (49590638337/50000000000 : ℝ) (991812766741/1000000000000 : ℝ) (495889487053/500000000000 : ℝ) (247944743527/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (541/4096 : ℝ)) 1 (49590638337/50000000000 : ℝ) (991812766741/1000000000000 : ℝ) (495889487053/500000000000 : ℝ) (247944743527/250000000000 : ℝ) (991795870423/1000000000000 : ℝ) (39671834817/40000000000 : ℝ) (991795870279/1000000000000 : ℝ) (991795870281/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (541/4096 : ℝ)) 2 (991795870423/1000000000000 : ℝ) (39671834817/40000000000 : ℝ) (991795870279/1000000000000 : ℝ) (991795870281/1000000000000 : ℝ) (991795870351/1000000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (541/4096 : ℝ)) 3 (991795870351/1000000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (541/4096 : ℝ)) 4 (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (541/4096 : ℝ)) 5 (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (541/4096 : ℝ)) 6 (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (541/4096 : ℝ)) 7 (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (541/4096 : ℝ))) (180224332109/1000000000000 : ℝ) (36044866423/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180224332109/1000000000000 : ℝ) (36044866423/200000000000 : ℝ) (295056083027/500000000000 : ℝ) (295056083029/500000000000 : ℝ) (106132091079/250000000000 : ℝ) (106132091081/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 1 (295056083027/500000000000 : ℝ) (295056083029/500000000000 : ℝ) (106132091079/250000000000 : ℝ) (106132091081/250000000000 : ℝ) (101464053037/200000000000 : ℝ) (507320265191/1000000000000 : ℝ) (50051908317/100000000000 : ℝ) (500519083177/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 2 (101464053037/200000000000 : ℝ) (507320265191/1000000000000 : ℝ) (50051908317/100000000000 : ℝ) (500519083177/1000000000000 : ℝ) (503919674177/1000000000000 : ℝ) (62989959273/125000000000 : ℝ) (62988524997/125000000000 : ℝ) (31494262499/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 3 (503919674177/1000000000000 : ℝ) (62989959273/125000000000 : ℝ) (62988524997/125000000000 : ℝ) (31494262499/62500000000 : ℝ) (125978484269/250000000000 : ℝ) (125978484271/250000000000 : ℝ) (503913937043/1000000000000 : ℝ) (125978484263/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 4 (125978484269/250000000000 : ℝ) (125978484271/250000000000 : ℝ) (503913937043/1000000000000 : ℝ) (125978484263/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 5 (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 6 (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (541/4096 : ℝ))) 7 (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (541/4096 : ℝ)) hmem 8 (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (541/4096 : ℝ))) hcmem 8 (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (541/4096 : ℝ)) (19835917407/20000000000 : ℝ) (991795870353/1000000000000 : ℝ) (503913937059/1000000000000 : ℝ) (125978484267/250000000000 : ℝ) (49880864161/62500000000 : ℝ) (399046913297/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1608_exp_lower
  have heNumeric : (1027473539261/500000000000 : ℝ)/4 ≤ Real.exp (-5328354128377/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027473539261/500000000000 : ℝ)/4 ≤ Real.exp ((4327/32768 : ℝ)-(399046913297/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4327/32768 : ℝ) (541/4096 : ℝ) (399046913297/500000000000 : ℝ) (1027473539261/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1609; no trusted numerical premise.
theorem cover8_leaf1609_exp_radius : (997937900995673457/1000000000000000000 : ℝ) ≤ Real.exp ((-4329/262144 : ℝ)/8) ∧ Real.exp ((-4329/262144 : ℝ)/8) ≤ (498968950497836729/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4329/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1609_exp_lower : (920116077136958761/1000000000000000000 : ℝ) ≤ Real.exp ((-26641742751/40000000000 : ℝ)/8) ∧ Real.exp ((-26641742751/40000000000 : ℝ)/8) ≤ (460058038568479381/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-26641742751/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1609_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102747425569/50000000000 : ℝ) ≤ 4*Real.exp (541/4096 : ℝ)*Real.exp (-mu (radius 8 (4329/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102747425569/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4329/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1609_exp_radius
  have hrNumeric : (983621781253/1000000000000 : ℝ) ≤ Real.exp (-4329/262144 : ℝ) ∧ Real.exp (-4329/262144 : ℝ) ≤ (491810890627/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983621781253/1000000000000 : ℝ) ≤ (radius 8 (4329/32768 : ℝ)) ∧ (radius 8 (4329/32768 : ℝ)) ≤ (491810890627/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4329/32768 : ℝ)) (983621781253/1000000000000 : ℝ) (491810890627/500000000000 : ℝ) (22530601219/125000000000 : ℝ) (90122404879/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4329/32768 : ℝ)) (983621781253/1000000000000 : ℝ) (491810890627/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983621781253/1000000000000 : ℝ) (491810890627/500000000000 : ℝ) (495905445313/500000000000 : ℝ) (991810890627/1000000000000 : ℝ) (991777082439/1000000000000 : ℝ) (991777082441/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 1 (495905445313/500000000000 : ℝ) (991810890627/1000000000000 : ℝ) (991777082439/1000000000000 : ℝ) (991777082441/1000000000000 : ℝ) (247948496633/250000000000 : ℝ) (495896993267/500000000000 : ℝ) (247948496597/250000000000 : ℝ) (99179398639/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 2 (247948496633/250000000000 : ℝ) (495896993267/500000000000 : ℝ) (247948496597/250000000000 : ℝ) (99179398639/100000000000 : ℝ) (49589699323/50000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 3 (49589699323/50000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 4 (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 5 (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 6 (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4329/32768 : ℝ)) 7 (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4329/32768 : ℝ))) (22530601219/125000000000 : ℝ) (90122404879/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22530601219/125000000000 : ℝ) (90122404879/500000000000 : ℝ) (147530601219/250000000000 : ℝ) (590122404879/1000000000000 : ℝ) (21227624087/50000000000 : ℝ) (106138120437/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 1 (147530601219/250000000000 : ℝ) (590122404879/1000000000000 : ℝ) (21227624087/50000000000 : ℝ) (106138120437/250000000000 : ℝ) (126834360827/250000000000 : ℝ) (253668721657/500000000000 : ℝ) (500537642461/1000000000000 : ℝ) (125134410617/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 2 (126834360827/250000000000 : ℝ) (253668721657/500000000000 : ℝ) (500537642461/1000000000000 : ℝ) (125134410617/250000000000 : ℝ) (125984385721/250000000000 : ℝ) (503937542891/1000000000000 : ℝ) (403140859/800000000 : ℝ) (503926073757/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 3 (125984385721/250000000000 : ℝ) (503937542891/1000000000000 : ℝ) (403140859/800000000 : ℝ) (503926073757/1000000000000 : ℝ) (503931808317/1000000000000 : ℝ) (125982952081/250000000000 : ℝ) (125982952071/250000000000 : ℝ) (125982952073/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 4 (503931808317/1000000000000 : ℝ) (125982952081/250000000000 : ℝ) (125982952071/250000000000 : ℝ) (125982952073/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 5 (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 6 (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4329/32768 : ℝ))) 7 (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4329/32768 : ℝ)) hmem 8 (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4329/32768 : ℝ))) hcmem 8 (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4329/32768 : ℝ)) (991793986459/1000000000000 : ℝ) (495896993231/500000000000 : ℝ) (5039318083/10000000000 : ℝ) (125982952077/250000000000 : ℝ) (199530911721/250000000000 : ℝ) (7981236469/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1609_exp_lower
  have heNumeric : (102747425569/50000000000 : ℝ)/4 ≤ Real.exp (-26641742751/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102747425569/50000000000 : ℝ)/4 ≤ Real.exp ((541/4096 : ℝ)-(7981236469/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (541/4096 : ℝ) (4329/32768 : ℝ) (7981236469/10000000000 : ℝ) (102747425569/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1610; no trusted numerical premise.
theorem cover8_leaf1610_exp_radius : (199587485028382827/200000000000000000 : ℝ) ≤ Real.exp ((-2165/131072 : ℝ)/8) ∧ Real.exp ((-2165/131072 : ℝ)/8) ≤ (124742178142739267/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2165/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1610_exp_lower : (460058078934958267/500000000000000000 : ℝ) ≤ Real.exp ((-5328342934703/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328342934703/8000000000000 : ℝ)/8) ≤ (184023231573983307/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328342934703/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1610_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82197998153/40000000000 : ℝ) ≤ 4*Real.exp (4329/32768 : ℝ)*Real.exp (-mu (radius 8 (2165/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (82197998153/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2165/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1610_exp_radius
  have hrNumeric : (983618029041/1000000000000 : ℝ) ≤ Real.exp (-2165/131072 : ℝ) ∧ Real.exp (-2165/131072 : ℝ) ≤ (491809014521/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983618029041/1000000000000 : ℝ) ≤ (radius 8 (2165/16384 : ℝ)) ∧ (radius 8 (2165/16384 : ℝ)) ≤ (491809014521/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2165/16384 : ℝ)) (983618029041/1000000000000 : ℝ) (491809014521/500000000000 : ℝ) (180265284909/1000000000000 : ℝ) (45066321229/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2165/16384 : ℝ)) (983618029041/1000000000000 : ℝ) (491809014521/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983618029041/1000000000000 : ℝ) (491809014521/500000000000 : ℝ) (24795225363/25000000000 : ℝ) (991809014521/1000000000000 : ℝ) (991775190777/1000000000000 : ℝ) (495887595389/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 1 (24795225363/25000000000 : ℝ) (991809014521/1000000000000 : ℝ) (991775190777/1000000000000 : ℝ) (495887595389/500000000000 : ℝ) (123974012831/125000000000 : ℝ) (19835842053/20000000000 : ℝ) (123974012813/125000000000 : ℝ) (495896051253/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 2 (123974012831/125000000000 : ℝ) (19835842053/20000000000 : ℝ) (123974012813/125000000000 : ℝ) (495896051253/500000000000 : ℝ) (61987006411/62500000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 3 (61987006411/62500000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 4 (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 5 (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 6 (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2165/16384 : ℝ)) 7 (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2165/16384 : ℝ))) (180265284909/1000000000000 : ℝ) (45066321229/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180265284909/1000000000000 : ℝ) (45066321229/250000000000 : ℝ) (295066321227/500000000000 : ℝ) (295066321229/500000000000 : ℝ) (424576594867/1000000000000 : ℝ) (106144148719/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 1 (295066321227/500000000000 : ℝ) (295066321229/500000000000 : ℝ) (424576594867/1000000000000 : ℝ) (106144148719/250000000000 : ℝ) (25367730933/50000000000 : ℝ) (507354618667/1000000000000 : ℝ) (15642381203/31250000000 : ℝ) (62569524813/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 2 (25367730933/50000000000 : ℝ) (507354618667/1000000000000 : ℝ) (15642381203/31250000000 : ℝ) (62569524813/125000000000 : ℝ) (251977704289/500000000000 : ℝ) (251977704293/500000000000 : ℝ) (503943944507/1000000000000 : ℝ) (125985986129/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 3 (251977704289/500000000000 : ℝ) (251977704293/500000000000 : ℝ) (503943944507/1000000000000 : ℝ) (125985986129/250000000000 : ℝ) (251974838271/500000000000 : ℝ) (503949676551/1000000000000 : ℝ) (503949676509/1000000000000 : ℝ) (503949676519/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 4 (251974838271/500000000000 : ℝ) (503949676551/1000000000000 : ℝ) (503949676509/1000000000000 : ℝ) (503949676519/1000000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 5 (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 6 (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2165/16384 : ℝ))) 7 (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2165/16384 : ℝ)) hmem 8 (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2165/16384 : ℝ))) hcmem 8 (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2165/16384 : ℝ)) (39671684103/40000000000 : ℝ) (495896051289/500000000000 : ℝ) (20157987061/40000000000 : ℝ) (100789935307/200000000000 : ℝ) (399076731261/500000000000 : ℝ) (798153462541/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1610_exp_lower
  have heNumeric : (82197998153/40000000000 : ℝ)/4 ≤ Real.exp (-5328342934703/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82197998153/40000000000 : ℝ)/4 ≤ Real.exp ((4329/32768 : ℝ)-(798153462541/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4329/32768 : ℝ) (2165/16384 : ℝ) (798153462541/1000000000000 : ℝ) (82197998153/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1611; no trusted numerical premise.
theorem cover8_leaf1611_exp_radius : (498968474644190859/500000000000000000 : ℝ) ≤ Real.exp ((-4331/262144 : ℝ)/8) ∧ Real.exp ((-4331/262144 : ℝ)/8) ≤ (997936949288381719/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4331/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1611_exp_lower : (920116239138504057/1000000000000000000 : ℝ) ≤ Real.exp ((-106566745639/160000000000 : ℝ)/8) ∧ Real.exp ((-106566745639/160000000000 : ℝ)/8) ≤ (460058119569252029/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-106566745639/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1611_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054951405841/1000000000000 : ℝ) ≤ 4*Real.exp (2165/16384 : ℝ)*Real.exp (-mu (radius 8 (4331/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054951405841/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4331/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1611_exp_radius
  have hrNumeric : (983614276843/1000000000000 : ℝ) ≤ Real.exp (-4331/262144 : ℝ) ∧ Real.exp (-4331/262144 : ℝ) ≤ (245903569211/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983614276843/1000000000000 : ℝ) ≤ (radius 8 (4331/32768 : ℝ)) ∧ (radius 8 (4331/32768 : ℝ)) ≤ (245903569211/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4331/32768 : ℝ)) (983614276843/1000000000000 : ℝ) (245903569211/250000000000 : ℝ) (90142878793/500000000000 : ℝ) (180285757593/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4331/32768 : ℝ)) (983614276843/1000000000000 : ℝ) (245903569211/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983614276843/1000000000000 : ℝ) (245903569211/250000000000 : ℝ) (991807138421/1000000000000 : ℝ) (495903569211/500000000000 : ℝ) (991773299117/1000000000000 : ℝ) (991773299119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 1 (991807138421/1000000000000 : ℝ) (495903569211/500000000000 : ℝ) (991773299117/1000000000000 : ℝ) (991773299119/1000000000000 : ℝ) (991790218769/1000000000000 : ℝ) (991790218771/1000000000000 : ℝ) (7748361083/7812500000 : ℝ) (991790218627/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 2 (991790218769/1000000000000 : ℝ) (991790218771/1000000000000 : ℝ) (7748361083/7812500000 : ℝ) (991790218627/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 3 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 4 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 5 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 6 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4331/32768 : ℝ)) 7 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4331/32768 : ℝ))) (90142878793/500000000000 : ℝ) (180285757593/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90142878793/500000000000 : ℝ) (180285757593/1000000000000 : ℝ) (590142878793/1000000000000 : ℝ) (590142878797/1000000000000 : ℝ) (53075087963/125000000000 : ℝ) (424600703713/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 1 (590142878793/1000000000000 : ℝ) (590142878797/1000000000000 : ℝ) (53075087963/125000000000 : ℝ) (424600703713/1000000000000 : ℝ) (31710736953/62500000000 : ℝ) (101474358251/200000000000 : ℝ) (250287375641/500000000000 : ℝ) (50057475129/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 2 (31710736953/62500000000 : ℝ) (101474358251/200000000000 : ℝ) (250287375641/500000000000 : ℝ) (50057475129/100000000000 : ℝ) (100794654253/200000000000 : ℝ) (503973271273/1000000000000 : ℝ) (100792362451/200000000000 : ℝ) (503961812263/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 3 (100794654253/200000000000 : ℝ) (503973271273/1000000000000 : ℝ) (100792362451/200000000000 : ℝ) (503961812263/1000000000000 : ℝ) (196862321/390625000 : ℝ) (62995942721/125000000000 : ℝ) (503967541727/1000000000000 : ℝ) (62995942717/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 4 (196862321/390625000 : ℝ) (62995942721/125000000000 : ℝ) (503967541727/1000000000000 : ℝ) (62995942717/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 5 (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 6 (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4331/32768 : ℝ))) 7 (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4331/32768 : ℝ)) hmem 8 (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4331/32768 : ℝ))) hcmem 8 (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4331/32768 : ℝ)) (123973777337/125000000000 : ℝ) (991790218699/1000000000000 : ℝ) (503967541743/1000000000000 : ℝ) (62995942719/125000000000 : ℝ) (798183273507/1000000000000 : ℝ) (31927330941/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1611_exp_lower
  have heNumeric : (2054951405841/1000000000000 : ℝ)/4 ≤ Real.exp (-106566745639/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054951405841/1000000000000 : ℝ)/4 ≤ Real.exp ((2165/16384 : ℝ)-(31927330941/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2165/16384 : ℝ) (4331/32768 : ℝ) (31927330941/40000000000 : ℝ) (2054951405841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1612; no trusted numerical premise.
theorem cover8_leaf1612_exp_radius : (498968236717538103/500000000000000000 : ℝ) ≤ Real.exp ((-1083/65536 : ℝ)/8) ∧ Real.exp ((-1083/65536 : ℝ)/8) ≤ (997936473435076207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1083/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1612_exp_lower : (460058160471705779/500000000000000000 : ℝ) ≤ Real.exp ((-5328331591893/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328331591893/8000000000000 : ℝ)/8) ≤ (920116320943411559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328331591893/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1612_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686910843/12500000000 : ℝ) ≤ 4*Real.exp (4331/32768 : ℝ)*Real.exp (-mu (radius 8 (1083/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (25686910843/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1083/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1612_exp_radius
  have hrNumeric : (49180526233/50000000000 : ℝ) ≤ Real.exp (-1083/65536 : ℝ) ∧ Real.exp (-1083/65536 : ℝ) ≤ (983610524661/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49180526233/50000000000 : ℝ) ≤ (radius 8 (1083/8192 : ℝ)) ∧ (radius 8 (1083/8192 : ℝ)) ≤ (983610524661/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1083/8192 : ℝ)) (49180526233/50000000000 : ℝ) (983610524661/1000000000000 : ℝ) (180306227779/1000000000000 : ℝ) (90153113893/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1083/8192 : ℝ)) (49180526233/50000000000 : ℝ) (983610524661/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49180526233/50000000000 : ℝ) (983610524661/1000000000000 : ℝ) (99180526233/100000000000 : ℝ) (991805262331/1000000000000 : ℝ) (495885703731/500000000000 : ℝ) (991771407463/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 1 (99180526233/100000000000 : ℝ) (991805262331/1000000000000 : ℝ) (495885703731/500000000000 : ℝ) (991771407463/1000000000000 : ℝ) (61986770931/62500000000 : ℝ) (991788334897/1000000000000 : ℝ) (991788334751/1000000000000 : ℝ) (991788334753/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 2 (61986770931/62500000000 : ℝ) (991788334897/1000000000000 : ℝ) (991788334751/1000000000000 : ℝ) (991788334753/1000000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 3 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 4 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 5 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 6 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1083/8192 : ℝ)) 7 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1083/8192 : ℝ))) (180306227779/1000000000000 : ℝ) (90153113893/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180306227779/1000000000000 : ℝ) (90153113893/500000000000 : ℝ) (590153113889/1000000000000 : ℝ) (590153113893/1000000000000 : ℝ) (424624808247/1000000000000 : ℝ) (6634762629/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 1 (590153113889/1000000000000 : ℝ) (590153113893/1000000000000 : ℝ) (424624808247/1000000000000 : ℝ) (6634762629/15625000000 : ℝ) (126847240267/250000000000 : ℝ) (20295558443/40000000000 : ℝ) (100118660163/200000000000 : ℝ) (500593300823/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 2 (126847240267/250000000000 : ℝ) (20295558443/40000000000 : ℝ) (100118660163/200000000000 : ℝ) (500593300823/1000000000000 : ℝ) (503991130941/1000000000000 : ℝ) (503991130949/1000000000000 : ℝ) (503979676989/1000000000000 : ℝ) (503979676997/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 3 (503991130941/1000000000000 : ℝ) (503991130949/1000000000000 : ℝ) (503979676989/1000000000000 : ℝ) (503979676997/1000000000000 : ℝ) (100797080793/200000000000 : ℝ) (503985403973/1000000000000 : ℝ) (125996350983/250000000000 : ℝ) (503985403941/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 4 (100797080793/200000000000 : ℝ) (503985403973/1000000000000 : ℝ) (125996350983/250000000000 : ℝ) (503985403941/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 5 (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 6 (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1083/8192 : ℝ))) 7 (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1083/8192 : ℝ)) hmem 8 (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1083/8192 : ℝ))) hcmem 8 (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1083/8192 : ℝ)) (991788334823/1000000000000 : ℝ) (39671533393/40000000000 : ℝ) (125996350987/250000000000 : ℝ) (503985403957/1000000000000 : ℝ) (798213079829/1000000000000 : ℝ) (399106539923/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1612_exp_lower
  have heNumeric : (25686910843/12500000000 : ℝ)/4 ≤ Real.exp (-5328331591893/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686910843/12500000000 : ℝ)/4 ≤ Real.exp ((4331/32768 : ℝ)-(399106539923/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4331/32768 : ℝ) (1083/8192 : ℝ) (399106539923/500000000000 : ℝ) (25686910843/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1613; no trusted numerical premise.
theorem cover8_leaf1613_exp_radius : (498967998790998799/500000000000000000 : ℝ) ≤ Real.exp ((-4333/262144 : ℝ)/8) ∧ Real.exp ((-4333/262144 : ℝ)/8) ≤ (997935997581997599/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4333/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1613_exp_lower : (920116403283143991/1000000000000000000 : ℝ) ≤ Real.exp ((-1332081466159/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332081466159/2000000000000 : ℝ)/8) ≤ (115014550410392999/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332081466159/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1613_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513738584649/250000000000 : ℝ) ≤ 4*Real.exp (1083/8192 : ℝ)*Real.exp (-mu (radius 8 (4333/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513738584649/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4333/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1613_exp_radius
  have hrNumeric : (983606772491/1000000000000 : ℝ) ≤ Real.exp (-4333/262144 : ℝ) ∧ Real.exp (-4333/262144 : ℝ) ≤ (245901693123/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983606772491/1000000000000 : ℝ) ≤ (radius 8 (4333/32768 : ℝ)) ∧ (radius 8 (4333/32768 : ℝ)) ≤ (245901693123/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4333/32768 : ℝ)) (983606772491/1000000000000 : ℝ) (245901693123/250000000000 : ℝ) (90163347747/500000000000 : ℝ) (360653391/2000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4333/32768 : ℝ)) (983606772491/1000000000000 : ℝ) (245901693123/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983606772491/1000000000000 : ℝ) (245901693123/250000000000 : ℝ) (198360677249/200000000000 : ℝ) (495901693123/500000000000 : ℝ) (99176951581/100000000000 : ℝ) (247942378953/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 1 (198360677249/200000000000 : ℝ) (495901693123/500000000000 : ℝ) (99176951581/100000000000 : ℝ) (247942378953/250000000000 : ℝ) (991786451027/1000000000000 : ℝ) (991786451029/1000000000000 : ℝ) (495893225441/500000000000 : ℝ) (198357290177/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 2 (991786451027/1000000000000 : ℝ) (991786451029/1000000000000 : ℝ) (495893225441/500000000000 : ℝ) (198357290177/200000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 3 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 4 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 5 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 6 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4333/32768 : ℝ)) 7 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4333/32768 : ℝ))) (90163347747/500000000000 : ℝ) (360653391/2000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90163347747/500000000000 : ℝ) (360653391/2000000000 : ℝ) (590163347747/1000000000000 : ℝ) (2360653391/4000000000 : ℝ) (53081113563/125000000000 : ℝ) (13270278391/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 1 (590163347747/1000000000000 : ℝ) (2360653391/4000000000 : ℝ) (53081113563/125000000000 : ℝ) (13270278391/31250000000 : ℝ) (162369961/320000000 : ℝ) (507406128131/1000000000000 : ℝ) (250305923551/500000000000 : ℝ) (500611847109/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 2 (162369961/320000000 : ℝ) (507406128131/1000000000000 : ℝ) (250305923551/500000000000 : ℝ) (500611847109/1000000000000 : ℝ) (504008987613/1000000000000 : ℝ) (25200449381/50000000000 : ℝ) (100799507743/200000000000 : ℝ) (503997538723/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 3 (504008987613/1000000000000 : ℝ) (25200449381/50000000000 : ℝ) (100799507743/200000000000 : ℝ) (503997538723/1000000000000 : ℝ) (126000815791/250000000000 : ℝ) (126000815793/250000000000 : ℝ) (504003263131/1000000000000 : ℝ) (504003263139/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 4 (126000815791/250000000000 : ℝ) (126000815793/250000000000 : ℝ) (504003263131/1000000000000 : ℝ) (504003263139/1000000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 5 (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 6 (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4333/32768 : ℝ))) 7 (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4333/32768 : ℝ)) hmem 8 (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4333/32768 : ℝ))) hcmem 8 (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4333/32768 : ℝ)) (495893225477/500000000000 : ℝ) (991786450957/1000000000000 : ℝ) (504003263147/1000000000000 : ℝ) (126000815789/250000000000 : ℝ) (798242881499/1000000000000 : ℝ) (798242881517/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1613_exp_lower
  have heNumeric : (513738584649/250000000000 : ℝ)/4 ≤ Real.exp (-1332081466159/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513738584649/250000000000 : ℝ)/4 ≤ Real.exp ((1083/8192 : ℝ)-(798242881517/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1083/8192 : ℝ) (4333/32768 : ℝ) (798242881517/1000000000000 : ℝ) (513738584649/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1614; no trusted numerical premise.
theorem cover8_leaf1614_exp_radius : (199587104345829179/200000000000000000 : ℝ) ≤ Real.exp ((-2167/131072 : ℝ)/8) ∧ Real.exp ((-2167/131072 : ℝ)/8) ≤ (124741940216143237/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2167/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1614_exp_lower : (184023297231563303/200000000000000000 : ℝ) ≤ Real.exp ((-5328320100171/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328320100171/8000000000000 : ℝ)/8) ≤ (230029121539454129/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328320100171/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1614_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054955819311/1000000000000 : ℝ) ≤ 4*Real.exp (4333/32768 : ℝ)*Real.exp (-mu (radius 8 (2167/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054955819311/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2167/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1614_exp_radius
  have hrNumeric : (61475188771/62500000000 : ℝ) ≤ Real.exp (-2167/131072 : ℝ) ∧ Real.exp (-2167/131072 : ℝ) ≤ (983603020337/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61475188771/62500000000 : ℝ) ≤ (radius 8 (2167/16384 : ℝ)) ∧ (radius 8 (2167/16384 : ℝ)) ≤ (983603020337/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2167/16384 : ℝ)) (61475188771/62500000000 : ℝ) (983603020337/1000000000000 : ℝ) (180347160731/1000000000000 : ℝ) (90173580369/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2167/16384 : ℝ)) (61475188771/62500000000 : ℝ) (983603020337/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61475188771/62500000000 : ℝ) (983603020337/1000000000000 : ℝ) (123975188771/125000000000 : ℝ) (991801510169/1000000000000 : ℝ) (495883812081/500000000000 : ℝ) (991767624163/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 1 (123975188771/125000000000 : ℝ) (991801510169/1000000000000 : ℝ) (495883812081/500000000000 : ℝ) (991767624163/1000000000000 : ℝ) (198356913433/200000000000 : ℝ) (495892283583/500000000000 : ℝ) (49589228351/50000000000 : ℝ) (495892283511/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 2 (198356913433/200000000000 : ℝ) (495892283583/500000000000 : ℝ) (49589228351/50000000000 : ℝ) (495892283511/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 3 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 4 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 5 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 6 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2167/16384 : ℝ)) 7 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2167/16384 : ℝ))) (180347160731/1000000000000 : ℝ) (90173580369/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180347160731/1000000000000 : ℝ) (90173580369/500000000000 : ℝ) (118034716073/200000000000 : ℝ) (590173580369/1000000000000 : ℝ) (106168251119/250000000000 : ℝ) (84934600897/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 1 (118034716073/200000000000 : ℝ) (590173580369/1000000000000 : ℝ) (106168251119/250000000000 : ℝ) (84934600897/200000000000 : ℝ) (25371164621/50000000000 : ℝ) (507423292427/1000000000000 : ℝ) (3911174923/7812500000 : ℝ) (62578798769/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 2 (25371164621/50000000000 : ℝ) (507423292427/1000000000000 : ℝ) (3911174923/7812500000 : ℝ) (62578798769/125000000000 : ℝ) (252013420641/500000000000 : ℝ) (50402684129/100000000000 : ℝ) (100803079487/200000000000 : ℝ) (126003849361/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 3 (252013420641/500000000000 : ℝ) (50402684129/100000000000 : ℝ) (100803079487/200000000000 : ℝ) (126003849361/250000000000 : ℝ) (252010559679/500000000000 : ℝ) (504021119367/1000000000000 : ℝ) (252010559663/500000000000 : ℝ) (100804223867/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 4 (252010559679/500000000000 : ℝ) (504021119367/1000000000000 : ℝ) (252010559663/500000000000 : ℝ) (100804223867/200000000000 : ℝ) (252010559671/500000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 5 (252010559671/500000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 6 (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2167/16384 : ℝ))) 7 (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2167/16384 : ℝ)) hmem 8 (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2167/16384 : ℝ))) hcmem 8 (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2167/16384 : ℝ)) (247946141773/250000000000 : ℝ) (495892283547/500000000000 : ℝ) (504021119341/1000000000000 : ℝ) (504021119351/1000000000000 : ℝ) (399136339259/500000000000 : ℝ) (798272678537/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1614_exp_lower
  have heNumeric : (2054955819311/1000000000000 : ℝ)/4 ≤ Real.exp (-5328320100171/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054955819311/1000000000000 : ℝ)/4 ≤ Real.exp ((4333/32768 : ℝ)-(798272678537/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4333/32768 : ℝ) (2167/16384 : ℝ) (798272678537/1000000000000 : ℝ) (2054955819311/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1615; no trusted numerical premise.
theorem cover8_leaf1615_exp_radius : (199587009175304219/200000000000000000 : ℝ) ≤ Real.exp ((-4335/262144 : ℝ)/8) ∧ Real.exp ((-4335/262144 : ℝ)/8) ≤ (124741880734565137/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4335/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1615_exp_lower : (230029142391799811/250000000000000000 : ℝ) ≤ Real.exp ((-2664157149257/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664157149257/4000000000000 : ℝ)/8) ≤ (184023313913439849/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664157149257/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1615_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102747865479/50000000000 : ℝ) ≤ 4*Real.exp (2167/16384 : ℝ)*Real.exp (-mu (radius 8 (4335/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102747865479/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4335/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1615_exp_radius
  have hrNumeric : (196719853639/200000000000 : ℝ) ≤ Real.exp (-4335/262144 : ℝ) ∧ Real.exp (-4335/262144 : ℝ) ≤ (245899817049/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196719853639/200000000000 : ℝ) ≤ (radius 8 (4335/32768 : ℝ)) ∧ (radius 8 (4335/32768 : ℝ)) ≤ (245899817049/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4335/32768 : ℝ)) (196719853639/200000000000 : ℝ) (245899817049/250000000000 : ℝ) (45091905873/250000000000 : ℝ) (90183811749/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4335/32768 : ℝ)) (196719853639/200000000000 : ℝ) (245899817049/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196719853639/200000000000 : ℝ) (245899817049/250000000000 : ℝ) (991799634097/1000000000000 : ℝ) (495899817049/500000000000 : ℝ) (991765732517/1000000000000 : ℝ) (495882866259/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 1 (991799634097/1000000000000 : ℝ) (495899817049/500000000000 : ℝ) (991765732517/1000000000000 : ℝ) (495882866259/500000000000 : ℝ) (991782683307/1000000000000 : ℝ) (247945670827/250000000000 : ℝ) (495891341581/500000000000 : ℝ) (247945670791/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 2 (991782683307/1000000000000 : ℝ) (247945670827/250000000000 : ℝ) (495891341581/500000000000 : ℝ) (247945670791/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 3 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 4 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 5 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 6 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4335/32768 : ℝ)) 7 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4335/32768 : ℝ))) (45091905873/250000000000 : ℝ) (90183811749/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45091905873/250000000000 : ℝ) (90183811749/500000000000 : ℝ) (295091905873/500000000000 : ℝ) (590183811749/1000000000000 : ℝ) (212348548083/500000000000 : ℝ) (212348548087/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 1 (295091905873/500000000000 : ℝ) (590183811749/1000000000000 : ℝ) (212348548083/500000000000 : ℝ) (212348548087/500000000000 : ℝ) (126860113489/250000000000 : ℝ) (253720226981/500000000000 : ℝ) (250324464971/500000000000 : ℝ) (500648929949/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 2 (126860113489/250000000000 : ℝ) (253720226981/500000000000 : ℝ) (250324464971/500000000000 : ℝ) (500648929949/1000000000000 : ℝ) (504044691949/1000000000000 : ℝ) (126011172989/250000000000 : ℝ) (504033253151/1000000000000 : ℝ) (252016626579/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 3 (504044691949/1000000000000 : ℝ) (126011172989/250000000000 : ℝ) (504033253151/1000000000000 : ℝ) (252016626579/500000000000 : ℝ) (10080779451/20000000000 : ℝ) (504038972557/1000000000000 : ℝ) (504038972517/1000000000000 : ℝ) (20161558901/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 4 (10080779451/20000000000 : ℝ) (504038972557/1000000000000 : ℝ) (504038972517/1000000000000 : ℝ) (20161558901/40000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 5 (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 6 (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4335/32768 : ℝ))) 7 (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4335/32768 : ℝ)) hmem 8 (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4335/32768 : ℝ))) hcmem 8 (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4335/32768 : ℝ)) (495891341617/500000000000 : ℝ) (247945670809/250000000000 : ℝ) (504038972533/1000000000000 : ℝ) (504038972541/1000000000000 : ℝ) (798302470893/1000000000000 : ℝ) (199575617727/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1615_exp_lower
  have heNumeric : (102747865479/50000000000 : ℝ)/4 ≤ Real.exp (-2664157149257/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102747865479/50000000000 : ℝ)/4 ≤ Real.exp ((2167/16384 : ℝ)-(199575617727/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2167/16384 : ℝ) (4335/32768 : ℝ) (199575617727/250000000000 : ℝ) (102747865479/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1616; no trusted numerical premise.
theorem cover8_leaf1616_exp_radius : (623709106265077/625000000000000 : ℝ) ≤ Real.exp ((-271/16384 : ℝ)/8) ∧ Real.exp ((-271/16384 : ℝ)/8) ≤ (997934570024123201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-271/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1616_exp_lower : (920116653511637369/1000000000000000000 : ℝ) ≤ Real.exp ((-5328308459641/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328308459641/8000000000000 : ℝ)/8) ≤ (92011665351163737/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328308459641/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1616_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205495880941/100000000000 : ℝ) ≤ 4*Real.exp (4335/32768 : ℝ)*Real.exp (-mu (radius 8 (271/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (205495880941/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (271/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1616_exp_radius
  have hrNumeric : (983595516069/1000000000000 : ℝ) ≤ Real.exp (-271/16384 : ℝ) ∧ Real.exp (-271/16384 : ℝ) ≤ (98359551607/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983595516069/1000000000000 : ℝ) ≤ (radius 8 (271/2048 : ℝ)) ∧ (radius 8 (271/2048 : ℝ)) ≤ (98359551607/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (271/2048 : ℝ)) (983595516069/1000000000000 : ℝ) (98359551607/100000000000 : ℝ) (45097020943/250000000000 : ℝ) (90194041889/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (271/2048 : ℝ)) (983595516069/1000000000000 : ℝ) (98359551607/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (271/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983595516069/1000000000000 : ℝ) (98359551607/100000000000 : ℝ) (495898879017/500000000000 : ℝ) (198359551607/200000000000 : ℝ) (7934110727/8000000000 : ℝ) (991763840877/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (271/2048 : ℝ)) 1 (495898879017/500000000000 : ℝ) (198359551607/200000000000 : ℝ) (7934110727/8000000000 : ℝ) (991763840877/1000000000000 : ℝ) (495890399727/500000000000 : ℝ) (30993149983/31250000000 : ℝ) (991780799309/1000000000000 : ℝ) (61986299957/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (271/2048 : ℝ)) 2 (495890399727/500000000000 : ℝ) (30993149983/31250000000 : ℝ) (991780799309/1000000000000 : ℝ) (61986299957/62500000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (271/2048 : ℝ)) 3 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (271/2048 : ℝ)) 4 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (271/2048 : ℝ)) 5 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (271/2048 : ℝ)) 6 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (271/2048 : ℝ)) 7 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (271/2048 : ℝ))) (45097020943/250000000000 : ℝ) (90194041889/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45097020943/250000000000 : ℝ) (90194041889/500000000000 : ℝ) (295097020943/500000000000 : ℝ) (590194041889/1000000000000 : ℝ) (26545073973/62500000000 : ℝ) (53090147947/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 1 (295097020943/500000000000 : ℝ) (590194041889/1000000000000 : ℝ) (26545073973/62500000000 : ℝ) (53090147947/125000000000 : ℝ) (507457612727/1000000000000 : ℝ) (507457612733/1000000000000 : ℝ) (500667466493/1000000000000 : ℝ) (1001334933/2000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 2 (507457612727/1000000000000 : ℝ) (507457612733/1000000000000 : ℝ) (500667466493/1000000000000 : ℝ) (1001334933/2000000000 : ℝ) (50406253961/100000000000 : ℝ) (504062539617/1000000000000 : ℝ) (504051105857/1000000000000 : ℝ) (100810221173/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 3 (50406253961/100000000000 : ℝ) (504062539617/1000000000000 : ℝ) (504051105857/1000000000000 : ℝ) (100810221173/200000000000 : ℝ) (504056822733/1000000000000 : ℝ) (504056822741/1000000000000 : ℝ) (504056822701/1000000000000 : ℝ) (504056822709/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 4 (504056822733/1000000000000 : ℝ) (504056822741/1000000000000 : ℝ) (504056822701/1000000000000 : ℝ) (504056822709/1000000000000 : ℝ) (504056822717/1000000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 5 (504056822717/1000000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 6 (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (271/2048 : ℝ))) 7 (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (271/2048 : ℝ)) hmem 8 (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (271/2048 : ℝ))) hcmem 8 (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (271/2048 : ℝ)) (991780799381/1000000000000 : ℝ) (123972599923/125000000000 : ℝ) (126014205679/250000000000 : ℝ) (20162272909/40000000000 : ℝ) (798332258609/1000000000000 : ℝ) (798332258627/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1616_exp_lower
  have heNumeric : (205495880941/100000000000 : ℝ)/4 ≤ Real.exp (-5328308459641/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205495880941/100000000000 : ℝ)/4 ≤ Real.exp ((4335/32768 : ℝ)-(798332258627/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4335/32768 : ℝ) (271/2048 : ℝ) (798332258627/1000000000000 : ℝ) (205495880941/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1617; no trusted numerical premise.
theorem cover8_leaf1617_exp_radius : (99793409417195221/100000000000000000 : ℝ) ≤ Real.exp ((-4337/262144 : ℝ)/8) ∧ Real.exp ((-4337/262144 : ℝ)/8) ≤ (997934094171952211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4337/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1617_exp_lower : (460058368995105459/500000000000000000 : ℝ) ≤ Real.exp ((-83254727869/125000000000 : ℝ)/8) ∧ Real.exp ((-83254727869/125000000000 : ℝ)/8) ≤ (920116737990210919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83254727869/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1617_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32108754981/15625000000 : ℝ) ≤ 4*Real.exp (271/2048 : ℝ)*Real.exp (-mu (radius 8 (4337/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (32108754981/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4337/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1617_exp_radius
  have hrNumeric : (983591763957/1000000000000 : ℝ) ≤ Real.exp (-4337/262144 : ℝ) ∧ Real.exp (-4337/262144 : ℝ) ≤ (491795881979/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983591763957/1000000000000 : ℝ) ≤ (radius 8 (4337/32768 : ℝ)) ∧ (radius 8 (4337/32768 : ℝ)) ≤ (491795881979/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4337/32768 : ℝ)) (983591763957/1000000000000 : ℝ) (491795881979/500000000000 : ℝ) (180408541577/1000000000000 : ℝ) (180408541583/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4337/32768 : ℝ)) (983591763957/1000000000000 : ℝ) (491795881979/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983591763957/1000000000000 : ℝ) (491795881979/500000000000 : ℝ) (495897940989/500000000000 : ℝ) (991795881979/1000000000000 : ℝ) (495880974619/500000000000 : ℝ) (991761949239/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 1 (495897940989/500000000000 : ℝ) (991795881979/1000000000000 : ℝ) (495880974619/500000000000 : ℝ) (991761949239/1000000000000 : ℝ) (123972364451/125000000000 : ℝ) (991778915609/1000000000000 : ℝ) (495889457731/500000000000 : ℝ) (123972364433/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 2 (123972364451/125000000000 : ℝ) (991778915609/1000000000000 : ℝ) (495889457731/500000000000 : ℝ) (123972364433/125000000000 : ℝ) (198355783107/200000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 3 (198355783107/200000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 4 (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 5 (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 6 (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4337/32768 : ℝ)) 7 (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4337/32768 : ℝ))) (180408541577/1000000000000 : ℝ) (180408541583/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180408541577/1000000000000 : ℝ) (180408541583/1000000000000 : ℝ) (147551067697/250000000000 : ℝ) (73775533849/125000000000 : ℝ) (424745266691/1000000000000 : ℝ) (424745266699/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 1 (147551067697/250000000000 : ℝ) (73775533849/125000000000 : ℝ) (424745266691/1000000000000 : ℝ) (424745266699/1000000000000 : ℝ) (507474768739/1000000000000 : ℝ) (253737384373/500000000000 : ℝ) (250342999901/500000000000 : ℝ) (500685999809/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 2 (507474768739/1000000000000 : ℝ) (253737384373/500000000000 : ℝ) (250342999901/500000000000 : ℝ) (500685999809/1000000000000 : ℝ) (50408038427/100000000000 : ℝ) (252040192139/500000000000 : ℝ) (504068955561/1000000000000 : ℝ) (504068955569/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 3 (50408038427/100000000000 : ℝ) (252040192139/500000000000 : ℝ) (504068955561/1000000000000 : ℝ) (504068955569/1000000000000 : ℝ) (100814933983/200000000000 : ℝ) (126018667481/250000000000 : ℝ) (504074669883/1000000000000 : ℝ) (126018667473/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 4 (100814933983/200000000000 : ℝ) (126018667481/250000000000 : ℝ) (504074669883/1000000000000 : ℝ) (126018667473/250000000000 : ℝ) (504074669899/1000000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 5 (504074669899/1000000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 6 (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4337/32768 : ℝ))) 7 (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4337/32768 : ℝ)) hmem 8 (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4337/32768 : ℝ))) hcmem 8 (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4337/32768 : ℝ)) (495889457767/500000000000 : ℝ) (991778915537/1000000000000 : ℝ) (252037334949/500000000000 : ℝ) (126018667477/250000000000 : ℝ) (399181020841/500000000000 : ℝ) (399181020851/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1617_exp_lower
  have heNumeric : (32108754981/15625000000 : ℝ)/4 ≤ Real.exp (-83254727869/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32108754981/15625000000 : ℝ)/4 ≤ Real.exp ((271/2048 : ℝ)-(399181020851/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (271/2048 : ℝ) (4337/32768 : ℝ) (399181020851/500000000000 : ℝ) (32108754981/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1618; no trusted numerical premise.
theorem cover8_leaf1618_exp_radius : (498966809160004061/500000000000000000 : ℝ) ≤ Real.exp ((-2169/131072 : ℝ)/8) ∧ Real.exp ((-2169/131072 : ℝ)/8) ≤ (997933618320008123/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2169/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1618_exp_lower : (230029205750787517/250000000000000000 : ℝ) ≤ Real.exp ((-5328296670423/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328296670423/8000000000000 : ℝ)/8) ≤ (920116823003150069/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328296670423/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1618_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054961837707/1000000000000 : ℝ) ≤ 4*Real.exp (4337/32768 : ℝ)*Real.exp (-mu (radius 8 (2169/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054961837707/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2169/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1618_exp_radius
  have hrNumeric : (983588011859/1000000000000 : ℝ) ≤ Real.exp (-2169/131072 : ℝ) ∧ Real.exp (-2169/131072 : ℝ) ≤ (49179400593/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983588011859/1000000000000 : ℝ) ≤ (radius 8 (2169/16384 : ℝ)) ∧ (radius 8 (2169/16384 : ℝ)) ≤ (49179400593/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2169/16384 : ℝ)) (983588011859/1000000000000 : ℝ) (49179400593/50000000000 : ℝ) (45107249227/250000000000 : ℝ) (90214498457/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2169/16384 : ℝ)) (983588011859/1000000000000 : ℝ) (49179400593/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983588011859/1000000000000 : ℝ) (49179400593/50000000000 : ℝ) (991794005929/1000000000000 : ℝ) (99179400593/100000000000 : ℝ) (247940014401/250000000000 : ℝ) (198352011521/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 1 (991794005929/1000000000000 : ℝ) (99179400593/100000000000 : ℝ) (247940014401/250000000000 : ℝ) (198352011521/200000000000 : ℝ) (495888515883/500000000000 : ℝ) (123972128971/125000000000 : ℝ) (991777031621/1000000000000 : ℝ) (991777031623/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 2 (495888515883/500000000000 : ℝ) (123972128971/125000000000 : ℝ) (991777031621/1000000000000 : ℝ) (991777031623/1000000000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 3 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 4 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 5 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 6 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2169/16384 : ℝ)) 7 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2169/16384 : ℝ))) (45107249227/250000000000 : ℝ) (90214498457/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45107249227/250000000000 : ℝ) (90214498457/500000000000 : ℝ) (295107249227/500000000000 : ℝ) (590214498457/1000000000000 : ℝ) (424769345537/1000000000000 : ℝ) (84953869109/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 1 (295107249227/500000000000 : ℝ) (590214498457/1000000000000 : ℝ) (424769345537/1000000000000 : ℝ) (84953869109/200000000000 : ℝ) (101498384399/200000000000 : ℝ) (507491922001/1000000000000 : ℝ) (31294033117/62500000000 : ℝ) (500704529879/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 2 (101498384399/200000000000 : ℝ) (507491922001/1000000000000 : ℝ) (31294033117/62500000000 : ℝ) (500704529879/1000000000000 : ℝ) (504098225933/1000000000000 : ℝ) (25204911297/50000000000 : ℝ) (504086802263/1000000000000 : ℝ) (504086802271/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 3 (504098225933/1000000000000 : ℝ) (25204911297/50000000000 : ℝ) (504086802263/1000000000000 : ℝ) (504086802271/1000000000000 : ℝ) (252046257049/500000000000 : ℝ) (252046257053/500000000000 : ℝ) (100818502813/200000000000 : ℝ) (252046257037/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 4 (252046257049/500000000000 : ℝ) (252046257053/500000000000 : ℝ) (100818502813/200000000000 : ℝ) (252046257037/500000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 5 (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 6 (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2169/16384 : ℝ))) 7 (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2169/16384 : ℝ)) hmem 8 (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2169/16384 : ℝ))) hcmem 8 (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2169/16384 : ℝ)) (991777031693/1000000000000 : ℝ) (61986064481/62500000000 : ℝ) (504092514081/1000000000000 : ℝ) (50409251409/100000000000 : ℝ) (399195910057/500000000000 : ℝ) (798391820131/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1618_exp_lower
  have heNumeric : (2054961837707/1000000000000 : ℝ)/4 ≤ Real.exp (-5328296670423/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054961837707/1000000000000 : ℝ)/4 ≤ Real.exp ((4337/32768 : ℝ)-(798391820131/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4337/32768 : ℝ) (2169/16384 : ℝ) (798391820131/1000000000000 : ℝ) (2054961837707/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1619; no trusted numerical premise.
theorem cover8_leaf1619_exp_radius : (49896633330840033/50000000000000000 : ℝ) ≤ Real.exp ((-1085/65536 : ℝ)/8) ∧ Real.exp ((-1085/65536 : ℝ)/8) ≤ (997932666616800661/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1085/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1619_exp_lower : (460056742335173463/500000000000000000 : ℝ) ≤ Real.exp ((-2664264436603/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664264436603/4000000000000 : ℝ)/8) ≤ (920113484670346927/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664264436603/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1619_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490219259/100000000000 : ℝ) ≤ 4*Real.exp (2169/16384 : ℝ)*Real.exp (-mu (radius 8 (1085/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (205490219259/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1085/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1619_exp_radius
  have hrNumeric : (983580507707/1000000000000 : ℝ) ≤ Real.exp (-1085/65536 : ℝ) ∧ Real.exp (-1085/65536 : ℝ) ≤ (245895126927/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983580507707/1000000000000 : ℝ) ≤ (radius 8 (1085/8192 : ℝ)) ∧ (radius 8 (1085/8192 : ℝ)) ≤ (245895126927/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1085/8192 : ℝ)) (983580507707/1000000000000 : ℝ) (245895126927/250000000000 : ℝ) (9023495007/50000000000 : ℝ) (180469900147/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1085/8192 : ℝ)) (983580507707/1000000000000 : ℝ) (245895126927/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983580507707/1000000000000 : ℝ) (245895126927/250000000000 : ℝ) (991790253853/1000000000000 : ℝ) (495895126927/500000000000 : ℝ) (991756274347/1000000000000 : ℝ) (247939068587/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 1 (991790253853/1000000000000 : ℝ) (495895126927/500000000000 : ℝ) (991756274347/1000000000000 : ℝ) (247939068587/250000000000 : ℝ) (9917732641/10000000000 : ℝ) (991773264101/1000000000000 : ℝ) (495886631977/500000000000 : ℝ) (247943315989/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 2 (9917732641/10000000000 : ℝ) (991773264101/1000000000000 : ℝ) (495886631977/500000000000 : ℝ) (247943315989/250000000000 : ℝ) (991773264027/1000000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 3 (991773264027/1000000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 4 (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 5 (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 6 (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1085/8192 : ℝ)) 7 (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1085/8192 : ℝ))) (9023495007/50000000000 : ℝ) (180469900147/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9023495007/50000000000 : ℝ) (180469900147/1000000000000 : ℝ) (59023495007/100000000000 : ℝ) (295117475037/500000000000 : ℝ) (106204372597/250000000000 : ℝ) (424817490397/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 1 (59023495007/100000000000 : ℝ) (295117475037/500000000000 : ℝ) (106204372597/250000000000 : ℝ) (424817490397/1000000000000 : ℝ) (507526220229/1000000000000 : ℝ) (126881555059/250000000000 : ℝ) (250370790143/500000000000 : ℝ) (250370790147/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 2 (507526220229/1000000000000 : ℝ) (126881555059/250000000000 : ℝ) (250370790143/500000000000 : ℝ) (250370790147/500000000000 : ℝ) (504133900257/1000000000000 : ℝ) (100826780053/200000000000 : ℝ) (504122486657/1000000000000 : ℝ) (252061243333/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 3 (504133900257/1000000000000 : ℝ) (100826780053/200000000000 : ℝ) (504122486657/1000000000000 : ℝ) (252061243333/500000000000 : ℝ) (504128193457/1000000000000 : ℝ) (252064096733/500000000000 : ℝ) (31508012089/62500000000 : ℝ) (252064096717/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 4 (504128193457/1000000000000 : ℝ) (252064096733/500000000000 : ℝ) (31508012089/62500000000 : ℝ) (252064096717/500000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 5 (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 6 (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1085/8192 : ℝ))) 7 (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1085/8192 : ℝ)) hmem 8 (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1085/8192 : ℝ))) hcmem 8 (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1085/8192 : ℝ)) (495886632013/500000000000 : ℝ) (991773264029/1000000000000 : ℝ) (3150801209/6250000000 : ℝ) (10082563869/20000000000 : ℝ) (399225681519/500000000000 : ℝ) (798451363057/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1619_exp_lower
  have heNumeric : (205490219259/100000000000 : ℝ)/4 ≤ Real.exp (-2664264436603/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490219259/100000000000 : ℝ)/4 ≤ Real.exp ((2169/16384 : ℝ)-(798451363057/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2169/16384 : ℝ) (1085/8192 : ℝ) (798451363057/1000000000000 : ℝ) (205490219259/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1620; no trusted numerical premise.
theorem cover8_leaf1620_exp_radius : (249482928728625203/250000000000000000 : ℝ) ≤ Real.exp ((-2171/131072 : ℝ)/8) ∧ Real.exp ((-2171/131072 : ℝ)/8) ≤ (997931714914500813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2171/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1620_exp_lower : (460056829216049227/500000000000000000 : ℝ) ≤ Real.exp ((-1332129196731/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332129196731/2000000000000 : ℝ)/8) ≤ (184022731686419691/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332129196731/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1620_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726324277/250000000000 : ℝ) ≤ 4*Real.exp (1085/8192 : ℝ)*Real.exp (-mu (radius 8 (2171/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513726324277/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2171/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1620_exp_radius
  have hrNumeric : (245893250903/250000000000 : ℝ) ≤ Real.exp (-2171/131072 : ℝ) ∧ Real.exp (-2171/131072 : ℝ) ≤ (983573003613/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245893250903/250000000000 : ℝ) ≤ (radius 8 (2171/16384 : ℝ)) ∧ (radius 8 (2171/16384 : ℝ)) ≤ (983573003613/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2171/16384 : ℝ)) (245893250903/250000000000 : ℝ) (983573003613/1000000000000 : ℝ) (90255396741/500000000000 : ℝ) (180510793489/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2171/16384 : ℝ)) (245893250903/250000000000 : ℝ) (983573003613/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245893250903/250000000000 : ℝ) (983573003613/1000000000000 : ℝ) (495893250903/500000000000 : ℝ) (991786501807/1000000000000 : ℝ) (30992265347/31250000000 : ℝ) (495876245553/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 1 (495893250903/500000000000 : ℝ) (991786501807/1000000000000 : ℝ) (30992265347/31250000000 : ℝ) (495876245553/500000000000 : ℝ) (198353899291/200000000000 : ℝ) (991769496457/1000000000000 : ℝ) (991769496309/1000000000000 : ℝ) (991769496311/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 2 (198353899291/200000000000 : ℝ) (991769496457/1000000000000 : ℝ) (991769496309/1000000000000 : ℝ) (991769496311/1000000000000 : ℝ) (495884748191/500000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 3 (495884748191/500000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 4 (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 5 (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 6 (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2171/16384 : ℝ)) 7 (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2171/16384 : ℝ))) (90255396741/500000000000 : ℝ) (180510793489/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90255396741/500000000000 : ℝ) (180510793489/1000000000000 : ℝ) (590255396741/1000000000000 : ℝ) (118051079349/200000000000 : ℝ) (84973123629/200000000000 : ℝ) (212432809077/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 1 (590255396741/1000000000000 : ℝ) (118051079349/200000000000 : ℝ) (84973123629/200000000000 : ℝ) (212432809077/500000000000 : ℝ) (507560507443/1000000000000 : ℝ) (10151210149/20000000000 : ℝ) (250389308877/500000000000 : ℝ) (250389308881/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 2 (507560507443/1000000000000 : ℝ) (10151210149/20000000000 : ℝ) (250389308877/500000000000 : ℝ) (250389308881/500000000000 : ℝ) (252084781299/500000000000 : ℝ) (252084781303/500000000000 : ℝ) (504158159057/1000000000000 : ℝ) (100831631813/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 3 (252084781299/500000000000 : ℝ) (252084781303/500000000000 : ℝ) (504158159057/1000000000000 : ℝ) (100831631813/200000000000 : ℝ) (504163860827/1000000000000 : ℝ) (126040965209/250000000000 : ℝ) (100832772159/200000000000 : ℝ) (126040965201/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 4 (504163860827/1000000000000 : ℝ) (126040965209/250000000000 : ℝ) (100832772159/200000000000 : ℝ) (126040965201/250000000000 : ℝ) (504163860811/1000000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 5 (504163860811/1000000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 6 (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2171/16384 : ℝ))) 7 (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2171/16384 : ℝ)) hmem 8 (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2171/16384 : ℝ))) hcmem 8 (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2171/16384 : ℝ)) (991769496381/1000000000000 : ℝ) (15496398381/15625000000 : ℝ) (50416386081/100000000000 : ℝ) (25208193041/50000000000 : ℝ) (798510887409/1000000000000 : ℝ) (199627721857/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1620_exp_lower
  have heNumeric : (513726324277/250000000000 : ℝ)/4 ≤ Real.exp (-1332129196731/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726324277/250000000000 : ℝ)/4 ≤ Real.exp ((1085/8192 : ℝ)-(199627721857/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1085/8192 : ℝ) (2171/16384 : ℝ) (199627721857/250000000000 : ℝ) (513726324277/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1621; no trusted numerical premise.
theorem cover8_leaf1621_exp_radius : (997930763213108577/1000000000000000000 : ℝ) ≤ Real.exp ((-543/32768 : ℝ)/8) ∧ Real.exp ((-543/32768 : ℝ)/8) ≤ (498965381606554289/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-543/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1621_exp_lower : (28753557322705989/31250000000000000 : ℝ) ≤ Real.exp ((-2664252276149/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664252276149/4000000000000 : ℝ)/8) ≤ (920113834326591649/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664252276149/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1621_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863554967/125000000000 : ℝ) ≤ 4*Real.exp (2171/16384 : ℝ)*Real.exp (-mu (radius 8 (543/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (256863554967/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (543/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1621_exp_radius
  have hrNumeric : (491782749787/500000000000 : ℝ) ≤ Real.exp (-543/32768 : ℝ) ∧ Real.exp (-543/32768 : ℝ) ≤ (39342619983/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491782749787/500000000000 : ℝ) ≤ (radius 8 (543/4096 : ℝ)) ∧ (radius 8 (543/4096 : ℝ)) ≤ (39342619983/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (543/4096 : ℝ)) (491782749787/500000000000 : ℝ) (39342619983/40000000000 : ℝ) (180551676939/1000000000000 : ℝ) (90275838473/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (543/4096 : ℝ)) (491782749787/500000000000 : ℝ) (39342619983/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (543/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491782749787/500000000000 : ℝ) (39342619983/40000000000 : ℝ) (991782749787/1000000000000 : ℝ) (247945687447/250000000000 : ℝ) (247937176969/250000000000 : ℝ) (991748707877/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (543/4096 : ℝ)) 1 (991782749787/1000000000000 : ℝ) (247945687447/250000000000 : ℝ) (247937176969/250000000000 : ℝ) (991748707877/1000000000000 : ℝ) (991765728831/1000000000000 : ℝ) (991765728833/1000000000000 : ℝ) (198353145737/200000000000 : ℝ) (991765728687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (543/4096 : ℝ)) 2 (991765728831/1000000000000 : ℝ) (991765728833/1000000000000 : ℝ) (198353145737/200000000000 : ℝ) (991765728687/1000000000000 : ℝ) (495882864379/500000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (543/4096 : ℝ)) 3 (495882864379/500000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (543/4096 : ℝ)) 4 (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (543/4096 : ℝ)) 5 (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (543/4096 : ℝ)) 6 (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (543/4096 : ℝ)) 7 (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (543/4096 : ℝ))) (180551676939/1000000000000 : ℝ) (90275838473/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180551676939/1000000000000 : ℝ) (90275838473/500000000000 : ℝ) (590275838469/1000000000000 : ℝ) (590275838473/1000000000000 : ℝ) (424913728819/1000000000000 : ℝ) (106228432207/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 1 (590275838469/1000000000000 : ℝ) (590275838473/1000000000000 : ℝ) (424913728819/1000000000000 : ℝ) (106228432207/250000000000 : ℝ) (126898695911/250000000000 : ℝ) (507594783651/1000000000000 : ℝ) (500815642283/1000000000000 : ℝ) (500815642291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 2 (126898695911/250000000000 : ℝ) (507594783651/1000000000000 : ℝ) (500815642283/1000000000000 : ℝ) (500815642291/1000000000000 : ℝ) (504205212963/1000000000000 : ℝ) (504205212971/1000000000000 : ℝ) (126048454867/250000000000 : ℝ) (126048454869/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 3 (504205212963/1000000000000 : ℝ) (504205212971/1000000000000 : ℝ) (126048454867/250000000000 : ℝ) (126048454869/250000000000 : ℝ) (100839903243/200000000000 : ℝ) (7878117441/15625000000 : ℝ) (504199516183/1000000000000 : ℝ) (15756234881/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 4 (100839903243/200000000000 : ℝ) (7878117441/15625000000 : ℝ) (504199516183/1000000000000 : ℝ) (15756234881/31250000000 : ℝ) (504199516199/1000000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 5 (504199516199/1000000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 6 (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (543/4096 : ℝ))) 7 (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (543/4096 : ℝ)) hmem 8 (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (543/4096 : ℝ))) hcmem 8 (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (543/4096 : ℝ)) (991765728757/1000000000000 : ℝ) (24794143219/25000000000 : ℝ) (252099758099/500000000000 : ℝ) (31512469763/62500000000 : ℝ) (798570393237/1000000000000 : ℝ) (99821299157/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1621_exp_lower
  have heNumeric : (256863554967/125000000000 : ℝ)/4 ≤ Real.exp (-2664252276149/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863554967/125000000000 : ℝ)/4 ≤ Real.exp ((2171/16384 : ℝ)-(99821299157/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2171/16384 : ℝ) (543/4096 : ℝ) (99821299157/125000000000 : ℝ) (256863554967/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1622; no trusted numerical premise.
theorem cover8_leaf1622_exp_radius : (199585962302524791/200000000000000000 : ℝ) ≤ Real.exp ((-2173/131072 : ℝ)/8) ∧ Real.exp ((-2173/131072 : ℝ)/8) ≤ (249482452878155989/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2173/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1622_exp_lower : (460057006175878737/500000000000000000 : ℝ) ≤ Real.exp ((-20814422537/31250000000 : ℝ)/8) ∧ Real.exp ((-20814422537/31250000000 : ℝ)/8) ≤ (36804560494070299/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-20814422537/31250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1622_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982324087/200000000000 : ℝ) ≤ 4*Real.exp (543/4096 : ℝ)*Real.exp (-mu (radius 8 (2173/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410982324087/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2173/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1622_exp_radius
  have hrNumeric : (983557995593/1000000000000 : ℝ) ≤ Real.exp (-2173/131072 : ℝ) ∧ Real.exp (-2173/131072 : ℝ) ≤ (491778997797/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983557995593/1000000000000 : ℝ) ≤ (radius 8 (2173/16384 : ℝ)) ∧ (radius 8 (2173/16384 : ℝ)) ≤ (491778997797/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2173/16384 : ℝ)) (983557995593/1000000000000 : ℝ) (491778997797/500000000000 : ℝ) (180592550519/1000000000000 : ℝ) (7223702021/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2173/16384 : ℝ)) (983557995593/1000000000000 : ℝ) (491778997797/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983557995593/1000000000000 : ℝ) (491778997797/500000000000 : ℝ) (247944749449/250000000000 : ℝ) (991778997797/1000000000000 : ℝ) (495872462331/500000000000 : ℝ) (991744924663/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 1 (247944749449/250000000000 : ℝ) (991778997797/1000000000000 : ℝ) (495872462331/500000000000 : ℝ) (991744924663/1000000000000 : ℝ) (991761961229/1000000000000 : ℝ) (99176196123/100000000000 : ℝ) (495880980541/500000000000 : ℝ) (247940490271/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 2 (991761961229/1000000000000 : ℝ) (99176196123/100000000000 : ℝ) (495880980541/500000000000 : ℝ) (247940490271/250000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 3 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 4 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 5 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 6 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2173/16384 : ℝ)) 7 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2173/16384 : ℝ))) (180592550519/1000000000000 : ℝ) (7223702021/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180592550519/1000000000000 : ℝ) (7223702021/40000000000 : ℝ) (590296275259/1000000000000 : ℝ) (590296275263/1000000000000 : ℝ) (16998472897/40000000000 : ℝ) (424961822433/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 1 (590296275259/1000000000000 : ℝ) (590296275263/1000000000000 : ℝ) (16998472897/40000000000 : ℝ) (424961822433/1000000000000 : ℝ) (253814524421/500000000000 : ℝ) (31726815553/62500000000 : ℝ) (250426326943/500000000000 : ℝ) (500852653893/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 2 (253814524421/500000000000 : ℝ) (31726815553/62500000000 : ℝ) (250426326943/500000000000 : ℝ) (500852653893/1000000000000 : ℝ) (126060212841/250000000000 : ℝ) (504240851371/1000000000000 : ℝ) (504229467903/1000000000000 : ℝ) (50422946791/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 3 (126060212841/250000000000 : ℝ) (504240851371/1000000000000 : ℝ) (504229467903/1000000000000 : ℝ) (50422946791/100000000000 : ℝ) (504235159633/1000000000000 : ℝ) (504235159641/1000000000000 : ℝ) (504235159601/1000000000000 : ℝ) (504235159609/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 4 (504235159633/1000000000000 : ℝ) (504235159641/1000000000000 : ℝ) (504235159601/1000000000000 : ℝ) (504235159609/1000000000000 : ℝ) (504235159617/1000000000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 5 (504235159617/1000000000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 6 (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2173/16384 : ℝ))) 7 (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2173/16384 : ℝ)) hmem 8 (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2173/16384 : ℝ))) hcmem 8 (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2173/16384 : ℝ)) (198352392231/200000000000 : ℝ) (991761961157/1000000000000 : ℝ) (7878674369/15625000000 : ℝ) (4033881277/8000000000 : ℝ) (399314940271/500000000000 : ℝ) (798629880559/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1622_exp_lower
  have heNumeric : (410982324087/200000000000 : ℝ)/4 ≤ Real.exp (-20814422537/31250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982324087/200000000000 : ℝ)/4 ≤ Real.exp ((543/4096 : ℝ)-(798629880559/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (543/4096 : ℝ) (2173/16384 : ℝ) (798629880559/1000000000000 : ℝ) (410982324087/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1623; no trusted numerical premise.
theorem cover8_leaf1623_exp_radius : (199585771962609389/200000000000000000 : ℝ) ≤ Real.exp ((-1087/65536 : ℝ)/8) ∧ Real.exp ((-1087/65536 : ℝ)/8) ≤ (498964429906523473/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1087/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1623_exp_lower : (92011419250679207/100000000000000000 : ℝ) ≤ Real.exp ((-2664239819251/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664239819251/4000000000000 : ℝ)/8) ≤ (920114192506792071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664239819251/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1623_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864354899/125000000000 : ℝ) ≤ 4*Real.exp (2173/16384 : ℝ)*Real.exp (-mu (radius 8 (1087/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256864354899/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1087/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1623_exp_radius
  have hrNumeric : (98355049167/100000000000 : ℝ) ≤ Real.exp (-1087/65536 : ℝ) ∧ Real.exp (-1087/65536 : ℝ) ≤ (983550491671/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98355049167/100000000000 : ℝ) ≤ (radius 8 (1087/8192 : ℝ)) ∧ (radius 8 (1087/8192 : ℝ)) ≤ (983550491671/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1087/8192 : ℝ)) (98355049167/100000000000 : ℝ) (983550491671/1000000000000 : ℝ) (90316707111/500000000000 : ℝ) (180633414229/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1087/8192 : ℝ)) (98355049167/100000000000 : ℝ) (983550491671/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98355049167/100000000000 : ℝ) (983550491671/1000000000000 : ℝ) (198355049167/200000000000 : ℝ) (247943811459/250000000000 : ℝ) (495870570731/500000000000 : ℝ) (123967642683/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 1 (198355049167/200000000000 : ℝ) (247943811459/250000000000 : ℝ) (495870570731/500000000000 : ℝ) (123967642683/125000000000 : ℝ) (61984887103/62500000000 : ℝ) (19835163873/20000000000 : ℝ) (991758193501/1000000000000 : ℝ) (30992443547/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 2 (61984887103/62500000000 : ℝ) (19835163873/20000000000 : ℝ) (991758193501/1000000000000 : ℝ) (30992443547/31250000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 3 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 4 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 5 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 6 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1087/8192 : ℝ)) 7 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1087/8192 : ℝ))) (90316707111/500000000000 : ℝ) (180633414229/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90316707111/500000000000 : ℝ) (180633414229/1000000000000 : ℝ) (590316707111/1000000000000 : ℝ) (118063341423/200000000000 : ℝ) (425009898969/1000000000000 : ℝ) (212504949489/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 1 (590316707111/1000000000000 : ℝ) (118063341423/200000000000 : ℝ) (425009898969/1000000000000 : ℝ) (212504949489/500000000000 : ℝ) (793223911/1562500000 : ℝ) (507663303047/1000000000000 : ℝ) (500889652567/1000000000000 : ℝ) (20035586103/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 2 (793223911/1562500000 : ℝ) (507663303047/1000000000000 : ℝ) (500889652567/1000000000000 : ℝ) (20035586103/40000000000 : ℝ) (504276477803/1000000000000 : ℝ) (504276477811/1000000000000 : ℝ) (100853020873/200000000000 : ℝ) (504265104373/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 3 (504276477803/1000000000000 : ℝ) (504276477811/1000000000000 : ℝ) (100853020873/200000000000 : ℝ) (504265104373/1000000000000 : ℝ) (126067697771/250000000000 : ℝ) (126067697773/250000000000 : ℝ) (504270791051/1000000000000 : ℝ) (25213539553/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 4 (126067697771/250000000000 : ℝ) (126067697773/250000000000 : ℝ) (504270791051/1000000000000 : ℝ) (25213539553/50000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 5 (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 6 (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1087/8192 : ℝ))) 7 (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1087/8192 : ℝ)) hmem 8 (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1087/8192 : ℝ))) hcmem 8 (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1087/8192 : ℝ)) (495879096787/500000000000 : ℝ) (991758193577/1000000000000 : ℝ) (504270791067/1000000000000 : ℝ) (126067697769/250000000000 : ℝ) (798689349327/1000000000000 : ℝ) (24959042167/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1623_exp_lower
  have heNumeric : (256864354899/125000000000 : ℝ)/4 ≤ Real.exp (-2664239819251/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864354899/125000000000 : ℝ)/4 ≤ Real.exp ((2173/16384 : ℝ)-(24959042167/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2173/16384 : ℝ) (1087/8192 : ℝ) (24959042167/31250000000 : ℝ) (256864354899/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1624; no trusted numerical premise.
theorem cover8_leaf1624_exp_radius : (997927908114377547/1000000000000000000 : ℝ) ≤ Real.exp ((-2175/131072 : ℝ)/8) ∧ Real.exp ((-2175/131072 : ℝ)/8) ≤ (249481977028594387/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2175/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1624_exp_lower : (920114374789051357/1000000000000000000 : ℝ) ≤ Real.exp ((-1332116739893/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332116739893/2000000000000 : ℝ)/8) ≤ (460057187394525679/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332116739893/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1624_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054918095959/1000000000000 : ℝ) ≤ 4*Real.exp (1087/8192 : ℝ)*Real.exp (-mu (radius 8 (2175/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054918095959/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2175/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1624_exp_radius
  have hrNumeric : (245885746951/250000000000 : ℝ) ≤ Real.exp (-2175/131072 : ℝ) ∧ Real.exp (-2175/131072 : ℝ) ≤ (196708597561/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245885746951/250000000000 : ℝ) ≤ (radius 8 (2175/16384 : ℝ)) ∧ (radius 8 (2175/16384 : ℝ)) ≤ (196708597561/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2175/16384 : ℝ)) (245885746951/250000000000 : ℝ) (196708597561/200000000000 : ℝ) (180674268061/1000000000000 : ℝ) (45168567017/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2175/16384 : ℝ)) (245885746951/250000000000 : ℝ) (196708597561/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245885746951/250000000000 : ℝ) (196708597561/200000000000 : ℝ) (495885746951/500000000000 : ℝ) (991771493903/1000000000000 : ℝ) (991737358277/1000000000000 : ℝ) (991737358279/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 1 (495885746951/500000000000 : ℝ) (991771493903/1000000000000 : ℝ) (991737358277/1000000000000 : ℝ) (991737358279/1000000000000 : ℝ) (991754426089/1000000000000 : ℝ) (991754426091/1000000000000 : ℝ) (495877212971/500000000000 : ℝ) (198350885189/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 2 (991754426089/1000000000000 : ℝ) (991754426091/1000000000000 : ℝ) (495877212971/500000000000 : ℝ) (198350885189/200000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 3 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 4 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 5 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 6 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2175/16384 : ℝ)) 7 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2175/16384 : ℝ))) (180674268061/1000000000000 : ℝ) (45168567017/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180674268061/1000000000000 : ℝ) (45168567017/250000000000 : ℝ) (59033713403/100000000000 : ℝ) (295168567017/500000000000 : ℝ) (53132244809/125000000000 : ℝ) (425057958481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 1 (59033713403/100000000000 : ℝ) (295168567017/500000000000 : ℝ) (53132244809/125000000000 : ℝ) (425057958481/1000000000000 : ℝ) (507697546251/1000000000000 : ℝ) (253848773129/500000000000 : ℝ) (250463319171/500000000000 : ℝ) (10018532767/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 2 (507697546251/1000000000000 : ℝ) (253848773129/500000000000 : ℝ) (250463319171/500000000000 : ℝ) (10018532767/20000000000 : ℝ) (63039011537/125000000000 : ℝ) (31519505769/62500000000 : ℝ) (504300728869/1000000000000 : ℝ) (504300728877/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 3 (63039011537/125000000000 : ℝ) (31519505769/62500000000 : ℝ) (504300728869/1000000000000 : ℝ) (504300728877/1000000000000 : ℝ) (252153205291/500000000000 : ℝ) (504306410591/1000000000000 : ℝ) (10086128211/20000000000 : ℝ) (504306410559/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 4 (252153205291/500000000000 : ℝ) (504306410591/1000000000000 : ℝ) (10086128211/20000000000 : ℝ) (504306410559/1000000000000 : ℝ) (252153205283/500000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 5 (252153205283/500000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 6 (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2175/16384 : ℝ))) 7 (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2175/16384 : ℝ)) hmem 8 (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2175/16384 : ℝ))) hcmem 8 (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2175/16384 : ℝ)) (198350885203/200000000000 : ℝ) (495877213009/500000000000 : ℝ) (100861282113/200000000000 : ℝ) (20172256423/40000000000 : ℝ) (399374399807/500000000000 : ℝ) (399374399817/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1624_exp_lower
  have heNumeric : (2054918095959/1000000000000 : ℝ)/4 ≤ Real.exp (-1332116739893/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054918095959/1000000000000 : ℝ)/4 ≤ Real.exp ((1087/8192 : ℝ)-(399374399817/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1087/8192 : ℝ) (2175/16384 : ℝ) (399374399817/500000000000 : ℝ) (2054918095959/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1600_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1600_certificate
#check SmaleRate.Proofs.cover8_leaf1601_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1601_certificate
#check SmaleRate.Proofs.cover8_leaf1602_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1602_certificate
#check SmaleRate.Proofs.cover8_leaf1603_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1603_certificate
#check SmaleRate.Proofs.cover8_leaf1604_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1604_certificate
#check SmaleRate.Proofs.cover8_leaf1605_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1605_certificate
#check SmaleRate.Proofs.cover8_leaf1606_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1606_certificate
#check SmaleRate.Proofs.cover8_leaf1607_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1607_certificate
#check SmaleRate.Proofs.cover8_leaf1608_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1608_certificate
#check SmaleRate.Proofs.cover8_leaf1609_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1609_certificate
#check SmaleRate.Proofs.cover8_leaf1610_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1610_certificate
#check SmaleRate.Proofs.cover8_leaf1611_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1611_certificate
#check SmaleRate.Proofs.cover8_leaf1612_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1612_certificate
#check SmaleRate.Proofs.cover8_leaf1613_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1613_certificate
#check SmaleRate.Proofs.cover8_leaf1614_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1614_certificate
#check SmaleRate.Proofs.cover8_leaf1615_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1615_certificate
#check SmaleRate.Proofs.cover8_leaf1616_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1616_certificate
#check SmaleRate.Proofs.cover8_leaf1617_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1617_certificate
#check SmaleRate.Proofs.cover8_leaf1618_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1618_certificate
#check SmaleRate.Proofs.cover8_leaf1619_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1619_certificate
#check SmaleRate.Proofs.cover8_leaf1620_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1620_certificate
#check SmaleRate.Proofs.cover8_leaf1621_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1621_certificate
#check SmaleRate.Proofs.cover8_leaf1622_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1622_certificate
#check SmaleRate.Proofs.cover8_leaf1623_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1623_certificate
#check SmaleRate.Proofs.cover8_leaf1624_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1624_certificate
