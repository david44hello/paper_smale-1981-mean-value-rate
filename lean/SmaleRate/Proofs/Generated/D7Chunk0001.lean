/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0025; no trusted numerical premise.
theorem cover7_leaf0025_exp_radius : (249470862800577591/250000000000000000 : ℝ) ≤ Real.exp ((-243/14336 : ℝ)/8) ∧ Real.exp ((-243/14336 : ℝ)/8) ≤ (199576690240462073/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-243/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0025_exp_lower : (36725148234903853/40000000000000000 : ℝ) ≤ Real.exp ((-170835391427/250000000000 : ℝ)/8) ∧ Real.exp ((-170835391427/250000000000 : ℝ)/8) ≤ (459064352936298163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170835391427/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0025_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504926923707/250000000000 : ℝ) ≤ 4*Real.exp (121/1024 : ℝ)*Real.exp (-mu (radius 7 (243/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (504926923707/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (243/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0025_exp_radius
  have hrNumeric : (491596256927/500000000000 : ℝ) ≤ Real.exp (-243/14336 : ℝ) ∧ Real.exp (-243/14336 : ℝ) ≤ (196638502771/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491596256927/500000000000 : ℝ) ≤ (radius 7 (243/2048 : ℝ)) ∧ (radius 7 (243/2048 : ℝ)) ≤ (196638502771/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (243/2048 : ℝ)) (491596256927/500000000000 : ℝ) (196638502771/200000000000 : ℝ) (91285925393/500000000000 : ℝ) (22821481349/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (243/2048 : ℝ)) (491596256927/500000000000 : ℝ) (196638502771/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (243/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491596256927/500000000000 : ℝ) (196638502771/200000000000 : ℝ) (991596256927/1000000000000 : ℝ) (30987383029/31250000000 : ℝ) (39662425823/40000000000 : ℝ) (123945080697/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (243/2048 : ℝ)) 1 (991596256927/1000000000000 : ℝ) (30987383029/31250000000 : ℝ) (39662425823/40000000000 : ℝ) (123945080697/125000000000 : ℝ) (991578451251/1000000000000 : ℝ) (247894612813/250000000000 : ℝ) (991578451091/1000000000000 : ℝ) (991578451093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (243/2048 : ℝ)) 2 (991578451251/1000000000000 : ℝ) (247894612813/250000000000 : ℝ) (991578451091/1000000000000 : ℝ) (991578451093/1000000000000 : ℝ) (991578451171/1000000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (243/2048 : ℝ)) 3 (991578451171/1000000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (243/2048 : ℝ)) 4 (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (243/2048 : ℝ)) 5 (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (243/2048 : ℝ)) 6 (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (243/2048 : ℝ)) 7 (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (243/2048 : ℝ))) (91285925393/500000000000 : ℝ) (22821481349/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91285925393/500000000000 : ℝ) (22821481349/125000000000 : ℝ) (591285925393/1000000000000 : ℝ) (147821481349/250000000000 : ℝ) (213642136987/500000000000 : ℝ) (213642136991/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 1 (591285925393/1000000000000 : ℝ) (147821481349/250000000000 : ℝ) (213642136987/500000000000 : ℝ) (213642136991/500000000000 : ℝ) (509285099683/1000000000000 : ℝ) (509285099689/1000000000000 : ℝ) (502640206651/1000000000000 : ℝ) (251320103329/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 2 (509285099683/1000000000000 : ℝ) (509285099689/1000000000000 : ℝ) (502640206651/1000000000000 : ℝ) (251320103329/500000000000 : ℝ) (505962653167/1000000000000 : ℝ) (252981326587/500000000000 : ℝ) (252975872243/500000000000 : ℝ) (252975872247/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 3 (505962653167/1000000000000 : ℝ) (252981326587/500000000000 : ℝ) (252975872243/500000000000 : ℝ) (252975872247/500000000000 : ℝ) (252978599413/500000000000 : ℝ) (252978599417/500000000000 : ℝ) (505957198797/1000000000000 : ℝ) (101191439761/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 4 (252978599413/500000000000 : ℝ) (252978599417/500000000000 : ℝ) (505957198797/1000000000000 : ℝ) (101191439761/200000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 5 (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 6 (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (243/2048 : ℝ))) 7 (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (243/2048 : ℝ)) hmem 8 (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (243/2048 : ℝ))) hcmem 8 (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (243/2048 : ℝ)) (99157845117/100000000000 : ℝ) (991578451173/1000000000000 : ℝ) (505957198811/1000000000000 : ℝ) (25297859941/50000000000 : ℝ) (80150562819/100000000000 : ℝ) (50094101763/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0025_exp_lower
  have heNumeric : (504926923707/250000000000 : ℝ)/4 ≤ Real.exp (-170835391427/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504926923707/250000000000 : ℝ)/4 ≤ Real.exp ((121/1024 : ℝ)-(50094101763/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (121/1024 : ℝ) (243/2048 : ℝ) (50094101763/62500000000 : ℝ) (504926923707/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0026; no trusted numerical premise.
theorem cover7_leaf0026_exp_radius : (249468687596762047/250000000000000000 : ℝ) ≤ Real.exp ((-61/3584 : ℝ)/8) ∧ Real.exp ((-61/3584 : ℝ)/8) ≤ (997874750387048189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-61/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0026_exp_lower : (36724933903106673/40000000000000000 : ℝ) ≤ Real.exp ((-683388254679/1000000000000 : ℝ)/8) ∧ Real.exp ((-683388254679/1000000000000 : ℝ)/8) ≤ (459061673788833413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683388254679/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0026_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403922679791/200000000000 : ℝ) ≤ 4*Real.exp (243/2048 : ℝ)*Real.exp (-mu (radius 7 (61/512 : ℝ))) ∧ (2019/1000 : ℝ) < (403922679791/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (61/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0026_exp_radius
  have hrNumeric : (491561967089/500000000000 : ℝ) ≤ Real.exp (-61/3584 : ℝ) ∧ Real.exp (-61/3584 : ℝ) ≤ (983123934179/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491561967089/500000000000 : ℝ) ≤ (radius 7 (61/512 : ℝ)) ∧ (radius 7 (61/512 : ℝ)) ≤ (983123934179/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (61/512 : ℝ)) (491561967089/500000000000 : ℝ) (983123934179/1000000000000 : ℝ) (182940782889/1000000000000 : ℝ) (11433798931/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (61/512 : ℝ)) (491561967089/500000000000 : ℝ) (983123934179/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (61/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491561967089/500000000000 : ℝ) (983123934179/1000000000000 : ℝ) (991561967089/1000000000000 : ℝ) (99156196709/100000000000 : ℝ) (991526063287/1000000000000 : ℝ) (123940757911/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (61/512 : ℝ)) 1 (991561967089/1000000000000 : ℝ) (99156196709/100000000000 : ℝ) (991526063287/1000000000000 : ℝ) (123940757911/125000000000 : ℝ) (247886003797/250000000000 : ℝ) (991544015189/1000000000000 : ℝ) (39661760601/40000000000 : ℝ) (991544015027/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (61/512 : ℝ)) 2 (247886003797/250000000000 : ℝ) (991544015189/1000000000000 : ℝ) (39661760601/40000000000 : ℝ) (991544015027/1000000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (61/512 : ℝ)) 3 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (61/512 : ℝ)) 4 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (61/512 : ℝ)) 5 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (61/512 : ℝ)) 6 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (61/512 : ℝ)) 7 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (61/512 : ℝ))) (182940782889/1000000000000 : ℝ) (11433798931/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182940782889/1000000000000 : ℝ) (11433798931/62500000000 : ℝ) (147867597861/250000000000 : ℝ) (73933798931/125000000000 : ℝ) (213857886743/500000000000 : ℝ) (85543154699/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 1 (147867597861/250000000000 : ℝ) (73933798931/125000000000 : ℝ) (213857886743/500000000000 : ℝ) (85543154699/200000000000 : ℝ) (101918616493/200000000000 : ℝ) (63699135309/125000000000 : ℝ) (251486190461/500000000000 : ℝ) (50297238093/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 2 (101918616493/200000000000 : ℝ) (63699135309/125000000000 : ℝ) (251486190461/500000000000 : ℝ) (50297238093/100000000000 : ℝ) (506282731693/1000000000000 : ℝ) (506282731701/1000000000000 : ℝ) (63283988643/125000000000 : ℝ) (15820997161/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 3 (506282731693/1000000000000 : ℝ) (506282731701/1000000000000 : ℝ) (63283988643/125000000000 : ℝ) (15820997161/31250000000 : ℝ) (253138660209/500000000000 : ℝ) (506277320427/1000000000000 : ℝ) (506277320389/1000000000000 : ℝ) (253138660199/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 4 (253138660209/500000000000 : ℝ) (506277320427/1000000000000 : ℝ) (506277320389/1000000000000 : ℝ) (253138660199/500000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 5 (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 6 (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (61/512 : ℝ))) 7 (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (61/512 : ℝ)) hmem 8 (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (61/512 : ℝ))) hcmem 8 (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (61/512 : ℝ)) (495772007553/500000000000 : ℝ) (247886003777/250000000000 : ℝ) (506277320403/1000000000000 : ℝ) (506277320413/1000000000000 : ℝ) (802040598411/1000000000000 : ℝ) (802040598429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0026_exp_lower
  have heNumeric : (403922679791/200000000000 : ℝ)/4 ≤ Real.exp (-683388254679/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403922679791/200000000000 : ℝ)/4 ≤ Real.exp ((243/2048 : ℝ)-(802040598429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (243/2048 : ℝ) (61/512 : ℝ) (802040598429/1000000000000 : ℝ) (403922679791/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0027; no trusted numerical premise.
theorem cover7_leaf0027_exp_radius : (997866049647650771/1000000000000000000 : ℝ) ≤ Real.exp ((-35/2048 : ℝ)/8) ∧ Real.exp ((-35/2048 : ℝ)/8) ≤ (249466512411912693/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-35/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0027_exp_lower : (918118158918993609/1000000000000000000 : ℝ) ≤ Real.exp ((-683433465801/1000000000000 : ℝ)/8) ∧ Real.exp ((-683433465801/1000000000000 : ℝ)/8) ≤ (91811815891899361/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683433465801/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0027_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1972189543/976562500 : ℝ) ≤ 4*Real.exp (61/512 : ℝ)*Real.exp (-mu (radius 7 (245/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1972189543/976562500 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (245/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0027_exp_radius
  have hrNumeric : (983055359287/1000000000000 : ℝ) ≤ Real.exp (-35/2048 : ℝ) ∧ Real.exp (-35/2048 : ℝ) ≤ (122881919911/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983055359287/1000000000000 : ℝ) ≤ (radius 7 (245/2048 : ℝ)) ∧ (radius 7 (245/2048 : ℝ)) ≤ (122881919911/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (245/2048 : ℝ)) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (245/2048 : ℝ)) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (245/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) (991527679643/1000000000000 : ℝ) (247881919911/250000000000 : ℝ) (198298296441/200000000000 : ℝ) (991491482207/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (245/2048 : ℝ)) 1 (991527679643/1000000000000 : ℝ) (247881919911/250000000000 : ℝ) (198298296441/200000000000 : ℝ) (991491482207/1000000000000 : ℝ) (247877395231/250000000000 : ℝ) (495754790463/500000000000 : ℝ) (495754790379/500000000000 : ℝ) (991509580761/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (245/2048 : ℝ)) 2 (247877395231/250000000000 : ℝ) (495754790463/500000000000 : ℝ) (495754790379/500000000000 : ℝ) (991509580761/1000000000000 : ℝ) (991509580841/1000000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (245/2048 : ℝ)) 3 (991509580841/1000000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (245/2048 : ℝ)) 4 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (245/2048 : ℝ)) 5 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (245/2048 : ℝ)) 6 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (245/2048 : ℝ)) 7 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (245/2048 : ℝ))) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ) (591654460577/1000000000000 : ℝ) (591654460581/1000000000000 : ℝ) (428145911057/1000000000000 : ℝ) (85629182213/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 1 (591654460577/1000000000000 : ℝ) (591654460581/1000000000000 : ℝ) (428145911057/1000000000000 : ℝ) (85629182213/200000000000 : ℝ) (509900185817/1000000000000 : ℝ) (509900185823/1000000000000 : ℝ) (251651762389/500000000000 : ℝ) (251651762393/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 2 (509900185817/1000000000000 : ℝ) (509900185823/1000000000000 : ℝ) (251651762389/500000000000 : ℝ) (251651762393/500000000000 : ℝ) (506601855297/1000000000000 : ℝ) (101320371061/200000000000 : ℝ) (50659111797/100000000000 : ℝ) (253295558989/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 3 (506601855297/1000000000000 : ℝ) (101320371061/200000000000 : ℝ) (50659111797/100000000000 : ℝ) (253295558989/500000000000 : ℝ) (506596486633/1000000000000 : ℝ) (253298243321/500000000000 : ℝ) (101319297321/200000000000 : ℝ) (253298243307/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 4 (506596486633/1000000000000 : ℝ) (253298243321/500000000000 : ℝ) (101319297321/200000000000 : ℝ) (253298243307/500000000000 : ℝ) (506596486619/1000000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 5 (506596486619/1000000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 6 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (245/2048 : ℝ))) 7 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (245/2048 : ℝ)) hmem 8 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (245/2048 : ℝ))) hcmem 8 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (245/2048 : ℝ)) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (802574090781/1000000000000 : ℝ) (802574090801/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0027_exp_lower
  have heNumeric : (1972189543/976562500 : ℝ)/4 ≤ Real.exp (-683433465801/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1972189543/976562500 : ℝ)/4 ≤ Real.exp ((61/512 : ℝ)-(802574090801/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (61/512 : ℝ) (245/2048 : ℝ) (802574090801/1000000000000 : ℝ) (1972189543/976562500 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0028; no trusted numerical premise.
theorem cover7_leaf0028_exp_radius : (997857348984117449/1000000000000000000 : ℝ) ≤ Real.exp ((-123/7168 : ℝ)/8) ∧ Real.exp ((-123/7168 : ℝ)/8) ≤ (19957146979682349/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-123/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0028_exp_lower : (918113138680070183/1000000000000000000 : ℝ) ≤ Real.exp ((-683477209649/1000000000000 : ℝ)/8) ∧ Real.exp ((-683477209649/1000000000000 : ℝ)/8) ≤ (114764142335008773/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683477209649/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0028_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019433752297/1000000000000 : ℝ) ≤ 4*Real.exp (245/2048 : ℝ)*Real.exp (-mu (radius 7 (123/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019433752297/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (123/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0028_exp_radius
  have hrNumeric : (491493394589/500000000000 : ℝ) ≤ Real.exp (-123/7168 : ℝ) ∧ Real.exp (-123/7168 : ℝ) ≤ (982986789179/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491493394589/500000000000 : ℝ) ≤ (radius 7 (123/1024 : ℝ)) ∧ (radius 7 (123/1024 : ℝ)) ≤ (982986789179/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (123/1024 : ℝ)) (491493394589/500000000000 : ℝ) (982986789179/1000000000000 : ℝ) (22959533797/125000000000 : ℝ) (183676270383/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (123/1024 : ℝ)) (491493394589/500000000000 : ℝ) (982986789179/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (123/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491493394589/500000000000 : ℝ) (982986789179/1000000000000 : ℝ) (991493394589/1000000000000 : ℝ) (99149339459/100000000000 : ℝ) (99145690233/100000000000 : ℝ) (991456902331/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (123/1024 : ℝ)) 1 (991493394589/1000000000000 : ℝ) (99149339459/100000000000 : ℝ) (99145690233/100000000000 : ℝ) (991456902331/1000000000000 : ℝ) (991475148459/1000000000000 : ℝ) (991475148461/1000000000000 : ℝ) (991475148291/1000000000000 : ℝ) (991475148293/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (123/1024 : ℝ)) 2 (991475148459/1000000000000 : ℝ) (991475148461/1000000000000 : ℝ) (991475148291/1000000000000 : ℝ) (991475148293/1000000000000 : ℝ) (7931801187/8000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (123/1024 : ℝ)) 3 (7931801187/8000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (123/1024 : ℝ)) 4 (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (123/1024 : ℝ)) 5 (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (123/1024 : ℝ)) 6 (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (123/1024 : ℝ)) 7 (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (123/1024 : ℝ))) (22959533797/125000000000 : ℝ) (183676270383/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22959533797/125000000000 : ℝ) (183676270383/1000000000000 : ℝ) (147959533797/250000000000 : ℝ) (73979766899/125000000000 : ℝ) (214287348189/500000000000 : ℝ) (428574696387/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 1 (147959533797/250000000000 : ℝ) (73979766899/125000000000 : ℝ) (214287348189/500000000000 : ℝ) (428574696387/1000000000000 : ℝ) (510206415783/1000000000000 : ℝ) (51020641579/100000000000 : ℝ) (503633645711/1000000000000 : ℝ) (503633645719/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 2 (510206415783/1000000000000 : ℝ) (51020641579/100000000000 : ℝ) (503633645711/1000000000000 : ℝ) (503633645719/1000000000000 : ℝ) (506920030747/1000000000000 : ℝ) (101384006151/200000000000 : ℝ) (101381875549/200000000000 : ℝ) (506909377753/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 3 (506920030747/1000000000000 : ℝ) (101384006151/200000000000 : ℝ) (101381875549/200000000000 : ℝ) (506909377753/1000000000000 : ℝ) (253457352123/500000000000 : ℝ) (253457352127/500000000000 : ℝ) (253457352109/500000000000 : ℝ) (506914704227/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 4 (253457352123/500000000000 : ℝ) (253457352127/500000000000 : ℝ) (253457352109/500000000000 : ℝ) (506914704227/1000000000000 : ℝ) (63364338029/125000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 5 (63364338029/125000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 6 (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (123/1024 : ℝ))) 7 (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (123/1024 : ℝ)) hmem 8 (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (123/1024 : ℝ))) hcmem 8 (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (123/1024 : ℝ)) (495737574187/500000000000 : ℝ) (991475148377/1000000000000 : ℝ) (506914704231/1000000000000 : ℝ) (506914704241/1000000000000 : ℝ) (803106115879/1000000000000 : ℝ) (803106115899/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0028_exp_lower
  have heNumeric : (2019433752297/1000000000000 : ℝ)/4 ≤ Real.exp (-683477209649/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019433752297/1000000000000 : ℝ)/4 ≤ Real.exp ((245/2048 : ℝ)-(803106115899/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (245/2048 : ℝ) (123/1024 : ℝ) (803106115899/1000000000000 : ℝ) (2019433752297/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0029; no trusted numerical premise.
theorem cover7_leaf0029_exp_radius : (997848648396447563/1000000000000000000 : ℝ) ≤ Real.exp ((-247/14336 : ℝ)/8) ∧ Real.exp ((-247/14336 : ℝ)/8) ≤ (249462162099111891/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-247/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0029_exp_lower : (114763535707758569/125000000000000000 : ℝ) ≤ Real.exp ((-136703899329/200000000000 : ℝ)/8) ∧ Real.exp ((-136703899329/200000000000 : ℝ)/8) ≤ (918108285662068553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136703899329/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0029_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403869671663/200000000000 : ℝ) ≤ 4*Real.exp (123/1024 : ℝ)*Real.exp (-mu (radius 7 (247/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403869671663/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (247/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0029_exp_radius
  have hrNumeric : (982918223853/1000000000000 : ℝ) ≤ Real.exp (-247/14336 : ℝ) ∧ Real.exp (-247/14336 : ℝ) ≤ (491459111927/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982918223853/1000000000000 : ℝ) ≤ (radius 7 (247/2048 : ℝ)) ∧ (radius 7 (247/2048 : ℝ)) ≤ (491459111927/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (247/2048 : ℝ)) (982918223853/1000000000000 : ℝ) (491459111927/500000000000 : ℝ) (92021417637/500000000000 : ℝ) (2300535441/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (247/2048 : ℝ)) (982918223853/1000000000000 : ℝ) (491459111927/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (247/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982918223853/1000000000000 : ℝ) (491459111927/500000000000 : ℝ) (495729555963/500000000000 : ℝ) (991459111927/1000000000000 : ℝ) (49571116183/50000000000 : ℝ) (495711161831/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (247/2048 : ℝ)) 1 (495729555963/500000000000 : ℝ) (991459111927/1000000000000 : ℝ) (49571116183/50000000000 : ℝ) (495711161831/500000000000 : ℝ) (991440717793/1000000000000 : ℝ) (198288143559/200000000000 : ℝ) (495720358811/500000000000 : ℝ) (123930089703/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (247/2048 : ℝ)) 2 (991440717793/1000000000000 : ℝ) (198288143559/200000000000 : ℝ) (495720358811/500000000000 : ℝ) (123930089703/125000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (247/2048 : ℝ)) 3 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (247/2048 : ℝ)) 4 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (247/2048 : ℝ)) 5 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (247/2048 : ℝ)) 6 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (247/2048 : ℝ)) 7 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (247/2048 : ℝ))) (92021417637/500000000000 : ℝ) (2300535441/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92021417637/500000000000 : ℝ) (2300535441/12500000000 : ℝ) (592021417637/1000000000000 : ℝ) (14800535441/25000000000 : ℝ) (3351579211/7812500000 : ℝ) (53625267377/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 1 (592021417637/1000000000000 : ℝ) (14800535441/25000000000 : ℝ) (3351579211/7812500000 : ℝ) (53625267377/125000000000 : ℝ) (255255889161/500000000000 : ℝ) (63813972291/125000000000 : ℝ) (125990687777/250000000000 : ℝ) (100792550223/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 2 (255255889161/500000000000 : ℝ) (63813972291/125000000000 : ℝ) (125990687777/250000000000 : ℝ) (100792550223/200000000000 : ℝ) (101447452943/200000000000 : ℝ) (253618632361/500000000000 : ℝ) (507226695153/1000000000000 : ℝ) (12680667379/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 3 (101447452943/200000000000 : ℝ) (253618632361/500000000000 : ℝ) (507226695153/1000000000000 : ℝ) (12680667379/25000000000 : ℝ) (253615989967/500000000000 : ℝ) (507231979941/1000000000000 : ℝ) (253615989953/500000000000 : ℝ) (253615989957/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 4 (253615989967/500000000000 : ℝ) (507231979941/1000000000000 : ℝ) (253615989953/500000000000 : ℝ) (253615989957/500000000000 : ℝ) (6340399749/12500000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 5 (6340399749/12500000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 6 (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (247/2048 : ℝ))) 7 (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (247/2048 : ℝ)) hmem 8 (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (247/2048 : ℝ))) hcmem 8 (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (247/2048 : ℝ)) (991440717707/1000000000000 : ℝ) (99144071771/100000000000 : ℝ) (507231979919/1000000000000 : ℝ) (63403997491/125000000000 : ℝ) (803636684127/1000000000000 : ℝ) (160727336829/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0029_exp_lower
  have heNumeric : (403869671663/200000000000 : ℝ)/4 ≤ Real.exp (-136703899329/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403869671663/200000000000 : ℝ)/4 ≤ Real.exp ((123/1024 : ℝ)-(160727336829/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (123/1024 : ℝ) (247/2048 : ℝ) (160727336829/200000000000 : ℝ) (403869671663/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0030; no trusted numerical premise.
theorem cover7_leaf0030_exp_radius : (997839947884640449/1000000000000000000 : ℝ) ≤ Real.exp ((-31/1792 : ℝ)/8) ∧ Real.exp ((-31/1792 : ℝ)/8) ≤ (19956798957692809/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-31/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0030_exp_lower : (114762949834475393/125000000000000000 : ℝ) ≤ Real.exp ((-85445042141/125000000000 : ℝ)/8) ∧ Real.exp ((-85445042141/125000000000 : ℝ)/8) ≤ (183620719735160629/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85445042141/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0030_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019265888837/1000000000000 : ℝ) ≤ 4*Real.exp (247/2048 : ℝ)*Real.exp (-mu (radius 7 (31/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019265888837/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (31/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0030_exp_radius
  have hrNumeric : (98284966331/100000000000 : ℝ) ≤ Real.exp (-31/1792 : ℝ) ∧ Real.exp (-31/1792 : ℝ) ≤ (982849663311/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98284966331/100000000000 : ℝ) ≤ (radius 7 (31/256 : ℝ)) ∧ (radius 7 (31/256 : ℝ)) ≤ (982849663311/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (31/256 : ℝ)) (98284966331/100000000000 : ℝ) (982849663311/1000000000000 : ℝ) (184408620539/1000000000000 : ℝ) (92204310273/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (31/256 : ℝ)) (98284966331/100000000000 : ℝ) (982849663311/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (31/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98284966331/100000000000 : ℝ) (982849663311/1000000000000 : ℝ) (198284966331/200000000000 : ℝ) (123928103957/125000000000 : ℝ) (991387746197/1000000000000 : ℝ) (495693873099/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (31/256 : ℝ)) 1 (198284966331/200000000000 : ℝ) (123928103957/125000000000 : ℝ) (991387746197/1000000000000 : ℝ) (495693873099/500000000000 : ℝ) (495703144463/500000000000 : ℝ) (991406288927/1000000000000 : ℝ) (61962893047/62500000000 : ℝ) (495703144377/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (31/256 : ℝ)) 2 (495703144463/500000000000 : ℝ) (991406288927/1000000000000 : ℝ) (61962893047/62500000000 : ℝ) (495703144377/500000000000 : ℝ) (991406288839/1000000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (31/256 : ℝ)) 3 (991406288839/1000000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (31/256 : ℝ)) 4 (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (31/256 : ℝ)) 5 (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (31/256 : ℝ)) 6 (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (31/256 : ℝ)) 7 (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (31/256 : ℝ))) (184408620539/1000000000000 : ℝ) (92204310273/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (184408620539/1000000000000 : ℝ) (92204310273/500000000000 : ℝ) (592204310269/1000000000000 : ℝ) (592204310273/1000000000000 : ℝ) (429428248417/1000000000000 : ℝ) (214714124213/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 1 (592204310269/1000000000000 : ℝ) (592204310273/1000000000000 : ℝ) (429428248417/1000000000000 : ℝ) (214714124213/500000000000 : ℝ) (510816279343/1000000000000 : ℝ) (10216325587/20000000000 : ℝ) (126072712071/250000000000 : ℝ) (126072712073/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 2 (510816279343/1000000000000 : ℝ) (10216325587/20000000000 : ℝ) (126072712071/250000000000 : ℝ) (126072712073/250000000000 : ℝ) (507553563813/1000000000000 : ℝ) (507553563821/1000000000000 : ℝ) (507543076819/1000000000000 : ℝ) (507543076827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 3 (507553563813/1000000000000 : ℝ) (507553563821/1000000000000 : ℝ) (507543076819/1000000000000 : ℝ) (507543076827/1000000000000 : ℝ) (126887080079/250000000000 : ℝ) (126887080081/250000000000 : ℝ) (15860885009/31250000000 : ℝ) (507548320297/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 4 (126887080079/250000000000 : ℝ) (126887080081/250000000000 : ℝ) (15860885009/31250000000 : ℝ) (507548320297/1000000000000 : ℝ) (253774160151/500000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 5 (253774160151/500000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 6 (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (31/256 : ℝ))) 7 (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (31/256 : ℝ)) hmem 8 (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (31/256 : ℝ))) hcmem 8 (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (31/256 : ℝ)) (495703144419/500000000000 : ℝ) (991406288841/1000000000000 : ℝ) (507548320301/1000000000000 : ℝ) (507548320311/1000000000000 : ℝ) (804165805859/1000000000000 : ℝ) (402082902939/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0030_exp_lower
  have heNumeric : (2019265888837/1000000000000 : ℝ)/4 ≤ Real.exp (-85445042141/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019265888837/1000000000000 : ℝ)/4 ≤ Real.exp ((247/2048 : ℝ)-(402082902939/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (247/2048 : ℝ) (31/256 : ℝ) (402082902939/500000000000 : ℝ) (2019265888837/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0031; no trusted numerical premise.
theorem cover7_leaf0031_exp_radius : (124728905931086931/125000000000000000 : ℝ) ≤ Real.exp ((-249/14336 : ℝ)/8) ∧ Real.exp ((-249/14336 : ℝ)/8) ≤ (997831247448695449/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-249/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0031_exp_lower : (183619815309470351/200000000000000000 : ℝ) ≤ Real.exp ((-136719948261/200000000000 : ℝ)/8) ∧ Real.exp ((-136719948261/200000000000 : ℝ)/8) ≤ (229524769136837939/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136719948261/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0031_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009593161447/500000000000 : ℝ) ≤ 4*Real.exp (31/256 : ℝ)*Real.exp (-mu (radius 7 (249/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009593161447/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (249/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0031_exp_radius
  have hrNumeric : (982781107549/1000000000000 : ℝ) ≤ Real.exp (-249/14336 : ℝ) ∧ Real.exp (-249/14336 : ℝ) ≤ (19655622151/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982781107549/1000000000000 : ℝ) ≤ (radius 7 (249/2048 : ℝ)) ∧ (radius 7 (249/2048 : ℝ)) ≤ (19655622151/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (249/2048 : ℝ)) (982781107549/1000000000000 : ℝ) (19655622151/20000000000 : ℝ) (18477363081/100000000000 : ℝ) (5774175963/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (249/2048 : ℝ)) (982781107549/1000000000000 : ℝ) (19655622151/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (249/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982781107549/1000000000000 : ℝ) (19655622151/20000000000 : ℝ) (495695276887/500000000000 : ℝ) (39655622151/40000000000 : ℝ) (991353169939/1000000000000 : ℝ) (49567658497/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (249/2048 : ℝ)) 1 (495695276887/500000000000 : ℝ) (39655622151/40000000000 : ℝ) (991353169939/1000000000000 : ℝ) (49567658497/50000000000 : ℝ) (30980370683/31250000000 : ℝ) (495685930929/500000000000 : ℝ) (12392148271/12500000000 : ℝ) (495685930841/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (249/2048 : ℝ)) 2 (30980370683/31250000000 : ℝ) (495685930929/500000000000 : ℝ) (12392148271/12500000000 : ℝ) (495685930841/500000000000 : ℝ) (123921482721/125000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (249/2048 : ℝ)) 3 (123921482721/125000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (249/2048 : ℝ)) 4 (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (249/2048 : ℝ)) 5 (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (249/2048 : ℝ)) 6 (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (249/2048 : ℝ)) 7 (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (249/2048 : ℝ))) (18477363081/100000000000 : ℝ) (5774175963/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18477363081/100000000000 : ℝ) (5774175963/31250000000 : ℝ) (118477363081/200000000000 : ℝ) (37024175963/62500000000 : ℝ) (214926516983/500000000000 : ℝ) (214926516987/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 1 (118477363081/200000000000 : ℝ) (37024175963/62500000000 : ℝ) (214926516983/500000000000 : ℝ) (214926516987/500000000000 : ℝ) (102223984937/200000000000 : ℝ) (511119924691/1000000000000 : ℝ) (63077243059/125000000000 : ℝ) (504617944479/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 2 (102223984937/200000000000 : ℝ) (511119924691/1000000000000 : ℝ) (63077243059/125000000000 : ℝ) (504617944479/1000000000000 : ℝ) (253934467289/500000000000 : ℝ) (101573786917/200000000000 : ℝ) (50785852929/100000000000 : ℝ) (253929264649/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 3 (253934467289/500000000000 : ℝ) (101573786917/200000000000 : ℝ) (50785852929/100000000000 : ℝ) (253929264649/500000000000 : ℝ) (253931865967/500000000000 : ℝ) (253931865971/500000000000 : ℝ) (507863731907/1000000000000 : ℝ) (101572746383/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 4 (253931865967/500000000000 : ℝ) (253931865971/500000000000 : ℝ) (507863731907/1000000000000 : ℝ) (101572746383/200000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 5 (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 6 (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (249/2048 : ℝ))) 7 (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (249/2048 : ℝ)) hmem 8 (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (249/2048 : ℝ))) hcmem 8 (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (249/2048 : ℝ)) (991371861767/1000000000000 : ℝ) (99137186177/100000000000 : ℝ) (6348296649/12500000000 : ℝ) (507863731929/1000000000000 : ℝ) (804693491287/1000000000000 : ℝ) (160938698261/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0031_exp_lower
  have heNumeric : (1009593161447/500000000000 : ℝ)/4 ≤ Real.exp (-136719948261/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009593161447/500000000000 : ℝ)/4 ≤ Real.exp ((31/256 : ℝ)-(160938698261/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (31/256 : ℝ) (249/2048 : ℝ) (160938698261/200000000000 : ℝ) (1009593161447/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0032; no trusted numerical premise.
theorem cover7_leaf0032_exp_radius : (124727818386076487/125000000000000000 : ℝ) ≤ Real.exp ((-125/7168 : ℝ)/8) ∧ Real.exp ((-125/7168 : ℝ)/8) ≤ (997822547088611897/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-125/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0032_exp_lower : (918094718117594007/1000000000000000000 : ℝ) ≤ Real.exp ((-136727543851/200000000000 : ℝ)/8) ∧ Real.exp ((-136727543851/200000000000 : ℝ)/8) ≤ (114761839764699251/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136727543851/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0032_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019109639793/1000000000000 : ℝ) ≤ 4*Real.exp (249/2048 : ℝ)*Real.exp (-mu (radius 7 (125/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019109639793/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (125/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0032_exp_radius
  have hrNumeric : (982712556571/1000000000000 : ℝ) ≤ Real.exp (-125/7168 : ℝ) ∧ Real.exp (-125/7168 : ℝ) ≤ (245678139143/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982712556571/1000000000000 : ℝ) ≤ (radius 7 (125/1024 : ℝ)) ∧ (radius 7 (125/1024 : ℝ)) ≤ (245678139143/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (125/1024 : ℝ)) (982712556571/1000000000000 : ℝ) (245678139143/250000000000 : ℝ) (46284467667/250000000000 : ℝ) (92568935337/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (125/1024 : ℝ)) (982712556571/1000000000000 : ℝ) (245678139143/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (125/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982712556571/1000000000000 : ℝ) (245678139143/250000000000 : ℝ) (198271255657/200000000000 : ℝ) (495678139143/500000000000 : ℝ) (123914824361/125000000000 : ℝ) (991318594889/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (125/1024 : ℝ)) 1 (198271255657/200000000000 : ℝ) (495678139143/500000000000 : ℝ) (123914824361/125000000000 : ℝ) (991318594889/1000000000000 : ℝ) (495668718293/500000000000 : ℝ) (247834359147/250000000000 : ℝ) (991337436407/1000000000000 : ℝ) (991337436409/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (125/1024 : ℝ)) 2 (495668718293/500000000000 : ℝ) (247834359147/250000000000 : ℝ) (991337436407/1000000000000 : ℝ) (991337436409/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (125/1024 : ℝ)) 3 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (125/1024 : ℝ)) 4 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (125/1024 : ℝ)) 5 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (125/1024 : ℝ)) 6 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (125/1024 : ℝ)) 7 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (125/1024 : ℝ))) (46284467667/250000000000 : ℝ) (92568935337/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46284467667/250000000000 : ℝ) (92568935337/500000000000 : ℝ) (296284467667/500000000000 : ℝ) (592568935337/1000000000000 : ℝ) (215138252449/500000000000 : ℝ) (215138252453/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 1 (296284467667/500000000000 : ℝ) (592568935337/1000000000000 : ℝ) (215138252449/500000000000 : ℝ) (215138252453/500000000000 : ℝ) (127855680029/250000000000 : ℝ) (255711360061/500000000000 : ℝ) (504944046807/1000000000000 : ℝ) (252472023407/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 2 (127855680029/250000000000 : ℝ) (255711360061/500000000000 : ℝ) (504944046807/1000000000000 : ℝ) (252472023407/500000000000 : ℝ) (508183383461/1000000000000 : ℝ) (127045845867/250000000000 : ℝ) (50817305903/100000000000 : ℝ) (254086529519/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 3 (508183383461/1000000000000 : ℝ) (127045845867/250000000000 : ℝ) (50817305903/100000000000 : ℝ) (254086529519/500000000000 : ℝ) (101635644249/200000000000 : ℝ) (508178221253/1000000000000 : ℝ) (508178221219/1000000000000 : ℝ) (508178221227/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 4 (101635644249/200000000000 : ℝ) (508178221253/1000000000000 : ℝ) (508178221219/1000000000000 : ℝ) (508178221227/1000000000000 : ℝ) (31761138827/62500000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 5 (31761138827/62500000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 6 (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (125/1024 : ℝ))) 7 (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (125/1024 : ℝ)) hmem 8 (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (125/1024 : ℝ))) hcmem 8 (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (125/1024 : ℝ)) (61958589781/62500000000 : ℝ) (991337436499/1000000000000 : ℝ) (508178221231/1000000000000 : ℝ) (12704455531/25000000000 : ℝ) (805219750487/1000000000000 : ℝ) (161043950101/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0032_exp_lower
  have heNumeric : (2019109639793/1000000000000 : ℝ)/4 ≤ Real.exp (-136727543851/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019109639793/1000000000000 : ℝ)/4 ≤ Real.exp ((249/2048 : ℝ)-(161043950101/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (249/2048 : ℝ) (125/1024 : ℝ) (161043950101/200000000000 : ℝ) (2019109639793/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0033; no trusted numerical premise.
theorem cover7_leaf0033_exp_radius : (498906923402194567/500000000000000000 : ℝ) ≤ Real.exp ((-251/14336 : ℝ)/8) ∧ Real.exp ((-251/14336 : ℝ)/8) ≤ (199562769360877827/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-251/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0033_exp_lower : (91809052223509371/100000000000000000 : ℝ) ≤ Real.exp ((-683674280991/1000000000000 : ℝ)/8) ∧ Real.exp ((-683674280991/1000000000000 : ℝ)/8) ≤ (918090522235093711/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683674280991/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0033_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019035818989/1000000000000 : ℝ) ≤ 4*Real.exp (125/1024 : ℝ)*Real.exp (-mu (radius 7 (251/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019035818989/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (251/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0033_exp_radius
  have hrNumeric : (982644010373/1000000000000 : ℝ) ≤ Real.exp (-251/14336 : ℝ) ∧ Real.exp (-251/14336 : ℝ) ≤ (491322005187/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982644010373/1000000000000 : ℝ) ≤ (radius 7 (251/2048 : ℝ)) ∧ (radius 7 (251/2048 : ℝ)) ≤ (491322005187/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (251/2048 : ℝ)) (982644010373/1000000000000 : ℝ) (491322005187/500000000000 : ℝ) (92750672337/500000000000 : ℝ) (4637533617/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (251/2048 : ℝ)) (982644010373/1000000000000 : ℝ) (491322005187/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (251/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982644010373/1000000000000 : ℝ) (491322005187/500000000000 : ℝ) (495661002593/500000000000 : ℝ) (991322005187/1000000000000 : ℝ) (991284021041/1000000000000 : ℝ) (991284021043/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (251/2048 : ℝ)) 1 (495661002593/500000000000 : ℝ) (991322005187/1000000000000 : ℝ) (991284021041/1000000000000 : ℝ) (991284021043/1000000000000 : ℝ) (991303013113/1000000000000 : ℝ) (198260602623/200000000000 : ℝ) (991303012931/1000000000000 : ℝ) (495651506467/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (251/2048 : ℝ)) 2 (991303013113/1000000000000 : ℝ) (198260602623/200000000000 : ℝ) (991303012931/1000000000000 : ℝ) (495651506467/500000000000 : ℝ) (495651506511/500000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (251/2048 : ℝ)) 3 (495651506511/500000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (251/2048 : ℝ)) 4 (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (251/2048 : ℝ)) 5 (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (251/2048 : ℝ)) 6 (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (251/2048 : ℝ)) 7 (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (251/2048 : ℝ))) (92750672337/500000000000 : ℝ) (4637533617/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92750672337/500000000000 : ℝ) (4637533617/25000000000 : ℝ) (592750672337/1000000000000 : ℝ) (29637533617/50000000000 : ℝ) (107674667597/250000000000 : ℝ) (86139734079/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 1 (592750672337/1000000000000 : ℝ) (29637533617/50000000000 : ℝ) (107674667597/250000000000 : ℝ) (86139734079/200000000000 : ℝ) (255862335681/500000000000 : ℝ) (63965583921/125000000000 : ℝ) (4042153299/8000000000 : ℝ) (505269162381/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 2 (255862335681/500000000000 : ℝ) (63965583921/125000000000 : ℝ) (4042153299/8000000000 : ℝ) (505269162381/1000000000000 : ℝ) (127124229217/250000000000 : ℝ) (813595067/1600000000 : ℝ) (63560834057/125000000000 : ℝ) (508486672463/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 3 (127124229217/250000000000 : ℝ) (813595067/1600000000 : ℝ) (63560834057/125000000000 : ℝ) (508486672463/1000000000000 : ℝ) (254245897331/500000000000 : ℝ) (508491794669/1000000000000 : ℝ) (127122948659/250000000000 : ℝ) (127122948661/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 4 (254245897331/500000000000 : ℝ) (508491794669/1000000000000 : ℝ) (127122948659/250000000000 : ℝ) (127122948661/250000000000 : ℝ) (508491794649/1000000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 5 (508491794649/1000000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 6 (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (251/2048 : ℝ))) 7 (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (251/2048 : ℝ)) hmem 8 (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (251/2048 : ℝ))) hcmem 8 (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (251/2048 : ℝ)) (991303013021/1000000000000 : ℝ) (39652120521/40000000000 : ℝ) (63561474331/125000000000 : ℝ) (508491794657/1000000000000 : ℝ) (805744593473/1000000000000 : ℝ) (805744593491/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0033_exp_lower
  have heNumeric : (2019035818989/1000000000000 : ℝ)/4 ≤ Real.exp (-683674280991/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019035818989/1000000000000 : ℝ)/4 ≤ Real.exp ((125/1024 : ℝ)-(805744593491/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (125/1024 : ℝ) (251/2048 : ℝ) (805744593491/1000000000000 : ℝ) (2019035818989/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0034; no trusted numerical premise.
theorem cover7_leaf0034_exp_radius : (498904748345362671/500000000000000000 : ℝ) ≤ Real.exp ((-503/28672 : ℝ)/8) ∧ Real.exp ((-503/28672 : ℝ)/8) ≤ (997809496690725343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-503/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0034_exp_lower : (918116503160376763/1000000000000000000 : ℝ) ≤ Real.exp ((-341723946613/500000000000 : ℝ)/8) ∧ Real.exp ((-341723946613/500000000000 : ℝ)/8) ≤ (229529125790094191/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341723946613/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0034_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009746477869/500000000000 : ℝ) ≤ 4*Real.exp (251/2048 : ℝ)*Real.exp (-mu (radius 7 (503/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009746477869/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (503/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0034_exp_radius
  have hrNumeric : (245652434767/250000000000 : ℝ) ≤ Real.exp (-503/28672 : ℝ) ∧ Real.exp (-503/28672 : ℝ) ≤ (982609739069/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245652434767/250000000000 : ℝ) ≤ (radius 7 (503/4096 : ℝ)) ∧ (radius 7 (503/4096 : ℝ)) ≤ (982609739069/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (503/4096 : ℝ)) (245652434767/250000000000 : ℝ) (982609739069/1000000000000 : ℝ) (92841397941/500000000000 : ℝ) (11605174743/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (503/4096 : ℝ)) (245652434767/250000000000 : ℝ) (982609739069/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (503/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245652434767/250000000000 : ℝ) (982609739069/1000000000000 : ℝ) (495652434767/500000000000 : ℝ) (198260973907/200000000000 : ℝ) (991266734571/1000000000000 : ℝ) (247816683643/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (503/4096 : ℝ)) 1 (495652434767/500000000000 : ℝ) (198260973907/200000000000 : ℝ) (991266734571/1000000000000 : ℝ) (247816683643/250000000000 : ℝ) (247821450513/250000000000 : ℝ) (495642901027/500000000000 : ℝ) (991285801869/1000000000000 : ℝ) (991285801871/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (503/4096 : ℝ)) 2 (247821450513/250000000000 : ℝ) (495642901027/500000000000 : ℝ) (991285801869/1000000000000 : ℝ) (991285801871/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (503/4096 : ℝ)) 3 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (503/4096 : ℝ)) 4 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (503/4096 : ℝ)) 5 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (503/4096 : ℝ)) 6 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (503/4096 : ℝ)) 7 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (503/4096 : ℝ))) (92841397941/500000000000 : ℝ) (11605174743/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92841397941/500000000000 : ℝ) (11605174743/62500000000 : ℝ) (592841397941/1000000000000 : ℝ) (74105174743/125000000000 : ℝ) (215454633207/500000000000 : ℝ) (215454633211/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 1 (592841397941/1000000000000 : ℝ) (74105174743/125000000000 : ℝ) (215454633207/500000000000 : ℝ) (215454633211/500000000000 : ℝ) (511875332177/1000000000000 : ℝ) (511875332183/1000000000000 : ℝ) (252715676149/500000000000 : ℝ) (101086270461/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 2 (511875332177/1000000000000 : ℝ) (511875332183/1000000000000 : ℝ) (252715676149/500000000000 : ℝ) (101086270461/200000000000 : ℝ) (508653342237/1000000000000 : ℝ) (127163335561/250000000000 : ℝ) (508643137523/1000000000000 : ℝ) (508643137531/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 3 (508653342237/1000000000000 : ℝ) (127163335561/250000000000 : ℝ) (508643137523/1000000000000 : ℝ) (508643137531/1000000000000 : ℝ) (12716205997/25000000000 : ℝ) (31790514993/62500000000 : ℝ) (254324119927/500000000000 : ℝ) (254324119931/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 4 (12716205997/25000000000 : ℝ) (31790514993/62500000000 : ℝ) (254324119927/500000000000 : ℝ) (254324119931/500000000000 : ℝ) (508648239867/1000000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 5 (508648239867/1000000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 6 (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (503/4096 : ℝ))) 7 (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (503/4096 : ℝ)) hmem 8 (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (503/4096 : ℝ))) hcmem 8 (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (503/4096 : ℝ)) (24782145049/25000000000 : ℝ) (991285801963/1000000000000 : ℝ) (254324119933/500000000000 : ℝ) (4069185919/8000000000 : ℝ) (403003243479/500000000000 : ℝ) (12593851359/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0034_exp_lower
  have heNumeric : (1009746477869/500000000000 : ℝ)/4 ≤ Real.exp (-341723946613/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009746477869/500000000000 : ℝ)/4 ≤ Real.exp ((251/2048 : ℝ)-(12593851359/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (251/2048 : ℝ) (503/4096 : ℝ) (12593851359/15625000000 : ℝ) (1009746477869/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0035; no trusted numerical premise.
theorem cover7_leaf0035_exp_radius : (997805146596026499/1000000000000000000 : ℝ) ≤ Real.exp ((-9/512 : ℝ)/8) ∧ Real.exp ((-9/512 : ℝ)/8) ≤ (1995610293192053/2000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0035_exp_lower : (918114505970980829/1000000000000000000 : ℝ) ≤ Real.exp ((-683465295737/1000000000000 : ℝ)/8) ∧ Real.exp ((-683465295737/1000000000000 : ℝ)/8) ≤ (91811450597098083/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683465295737/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0035_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504864452949/250000000000 : ℝ) ≤ 4*Real.exp (503/4096 : ℝ)*Real.exp (-mu (radius 7 (63/512 : ℝ))) ∧ (2019/1000 : ℝ) < (504864452949/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (63/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0035_exp_radius
  have hrNumeric : (982575468957/1000000000000 : ℝ) ≤ Real.exp (-9/512 : ℝ) ∧ Real.exp (-9/512 : ℝ) ≤ (491287734479/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982575468957/1000000000000 : ℝ) ≤ (radius 7 (63/512 : ℝ)) ∧ (radius 7 (63/512 : ℝ)) ≤ (491287734479/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (63/512 : ℝ)) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (63/512 : ℝ)) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (63/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) (495643867239/500000000000 : ℝ) (991287734479/1000000000000 : ℝ) (991249448401/1000000000000 : ℝ) (991249448403/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (63/512 : ℝ)) 1 (495643867239/500000000000 : ℝ) (991287734479/1000000000000 : ℝ) (991249448401/1000000000000 : ℝ) (991249448403/1000000000000 : ℝ) (991268591439/1000000000000 : ℝ) (991268591441/1000000000000 : ℝ) (495634295627/500000000000 : ℝ) (991268591257/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (63/512 : ℝ)) 2 (991268591439/1000000000000 : ℝ) (991268591441/1000000000000 : ℝ) (495634295627/500000000000 : ℝ) (991268591257/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (63/512 : ℝ)) 3 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (63/512 : ℝ)) 4 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (63/512 : ℝ)) 5 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (63/512 : ℝ)) 6 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (63/512 : ℝ)) 7 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (63/512 : ℝ))) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ) (296466014329/500000000000 : ℝ) (592932028661/1000000000000 : ℝ) (431119539473/1000000000000 : ℝ) (431119539481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 1 (296466014329/500000000000 : ℝ) (592932028661/1000000000000 : ℝ) (431119539473/1000000000000 : ℝ) (431119539481/1000000000000 : ℝ) (102405156813/200000000000 : ℝ) (512025784071/1000000000000 : ℝ) (505593298149/1000000000000 : ℝ) (126398324539/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 2 (102405156813/200000000000 : ℝ) (512025784071/1000000000000 : ℝ) (505593298149/1000000000000 : ℝ) (126398324539/250000000000 : ℝ) (508809541107/1000000000000 : ℝ) (254404770557/500000000000 : ℝ) (254399687943/500000000000 : ℝ) (254399687947/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 3 (508809541107/1000000000000 : ℝ) (254404770557/500000000000 : ℝ) (254399687943/500000000000 : ℝ) (254399687947/500000000000 : ℝ) (248439677/488281250 : ℝ) (63600557313/125000000000 : ℝ) (508804458471/1000000000000 : ℝ) (508804458479/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 4 (248439677/488281250 : ℝ) (63600557313/125000000000 : ℝ) (508804458471/1000000000000 : ℝ) (508804458479/1000000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 5 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 6 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (63/512 : ℝ))) 7 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (63/512 : ℝ)) hmem 8 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (63/512 : ℝ))) hcmem 8 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (63/512 : ℝ)) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (403134015047/500000000000 : ℝ) (25195875941/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0035_exp_lower
  have heNumeric : (504864452949/250000000000 : ℝ)/4 ≤ Real.exp (-683465295737/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504864452949/250000000000 : ℝ)/4 ≤ Real.exp ((503/4096 : ℝ)-(25195875941/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (503/4096 : ℝ) (63/512 : ℝ) (25195875941/31250000000 : ℝ) (504864452949/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0036; no trusted numerical premise.
theorem cover7_leaf0036_exp_radius : (997800796520292523/1000000000000000000 : ℝ) ≤ Real.exp ((-505/28672 : ℝ)/8) ∧ Real.exp ((-505/28672 : ℝ)/8) ≤ (249450199130073131/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-505/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0036_exp_lower : (57382034303509211/62500000000000000 : ℝ) ≤ Real.exp ((-136696469819/200000000000 : ℝ)/8) ∧ Real.exp ((-136696469819/200000000000 : ℝ)/8) ≤ (918112548856147377/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136696469819/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0036_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126213960847/62500000000 : ℝ) ≤ 4*Real.exp (63/512 : ℝ)*Real.exp (-mu (radius 7 (505/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (126213960847/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (505/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0036_exp_radius
  have hrNumeric : (491270600021/500000000000 : ℝ) ≤ Real.exp (-505/28672 : ℝ) ∧ Real.exp (-505/28672 : ℝ) ≤ (982541200043/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491270600021/500000000000 : ℝ) ≤ (radius 7 (505/4096 : ℝ)) ∧ (radius 7 (505/4096 : ℝ)) ≤ (982541200043/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (505/4096 : ℝ)) (491270600021/500000000000 : ℝ) (982541200043/1000000000000 : ℝ) (186045129519/1000000000000 : ℝ) (93022564763/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (505/4096 : ℝ)) (491270600021/500000000000 : ℝ) (982541200043/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (505/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491270600021/500000000000 : ℝ) (982541200043/1000000000000 : ℝ) (991270600021/1000000000000 : ℝ) (495635300011/500000000000 : ℝ) (495616081267/500000000000 : ℝ) (198246432507/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (505/4096 : ℝ)) 1 (991270600021/1000000000000 : ℝ) (495635300011/500000000000 : ℝ) (495616081267/500000000000 : ℝ) (198246432507/200000000000 : ℝ) (991251381277/1000000000000 : ℝ) (991251381279/1000000000000 : ℝ) (991251381091/1000000000000 : ℝ) (991251381093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (505/4096 : ℝ)) 2 (991251381277/1000000000000 : ℝ) (991251381279/1000000000000 : ℝ) (991251381091/1000000000000 : ℝ) (991251381093/1000000000000 : ℝ) (15488302831/15625000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (505/4096 : ℝ)) 3 (15488302831/15625000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (505/4096 : ℝ)) 4 (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (505/4096 : ℝ)) 5 (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (505/4096 : ℝ)) 6 (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (505/4096 : ℝ)) 7 (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (505/4096 : ℝ))) (186045129519/1000000000000 : ℝ) (93022564763/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (186045129519/1000000000000 : ℝ) (93022564763/500000000000 : ℝ) (593022564759/1000000000000 : ℝ) (593022564763/1000000000000 : ℝ) (215664745333/500000000000 : ℝ) (107832372669/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 1 (593022564759/1000000000000 : ℝ) (593022564763/1000000000000 : ℝ) (215664745333/500000000000 : ℝ) (107832372669/250000000000 : ℝ) (8002750433/15625000000 : ℝ) (12804400693/25000000000 : ℝ) (505755000777/1000000000000 : ℝ) (101151000157/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 2 (8002750433/15625000000 : ℝ) (12804400693/25000000000 : ℝ) (505755000777/1000000000000 : ℝ) (101151000157/200000000000 : ℝ) (127241378561/250000000000 : ℝ) (508965514253/1000000000000 : ℝ) (508955388313/1000000000000 : ℝ) (254477694161/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 3 (127241378561/250000000000 : ℝ) (508965514253/1000000000000 : ℝ) (508955388313/1000000000000 : ℝ) (254477694161/500000000000 : ℝ) (254480225639/500000000000 : ℝ) (63620056411/125000000000 : ℝ) (508960451253/1000000000000 : ℝ) (508960451263/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 4 (254480225639/500000000000 : ℝ) (63620056411/125000000000 : ℝ) (508960451253/1000000000000 : ℝ) (508960451263/1000000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 5 (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 6 (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (505/4096 : ℝ))) 7 (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (505/4096 : ℝ)) hmem 8 (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (505/4096 : ℝ))) hcmem 8 (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (505/4096 : ℝ)) (991251381183/1000000000000 : ℝ) (495625690593/500000000000 : ℝ) (101792090253/200000000000 : ℝ) (127240112819/250000000000 : ℝ) (403264612037/500000000000 : ℝ) (161305844819/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0036_exp_lower
  have heNumeric : (126213960847/62500000000 : ℝ)/4 ≤ Real.exp (-136696469819/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126213960847/62500000000 : ℝ)/4 ≤ Real.exp ((63/512 : ℝ)-(161305844819/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (63/512 : ℝ) (505/4096 : ℝ) (161305844819/200000000000 : ℝ) (126213960847/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0037; no trusted numerical premise.
theorem cover7_leaf0037_exp_radius : (99779644646352333/100000000000000000 : ℝ) ≤ Real.exp ((-253/14336 : ℝ)/8) ∧ Real.exp ((-253/14336 : ℝ)/8) ≤ (997796446463523331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-253/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0037_exp_lower : (459055315837976283/500000000000000000 : ℝ) ≤ Real.exp ((-683499054517/1000000000000 : ℝ)/8) ∧ Real.exp ((-683499054517/1000000000000 : ℝ)/8) ≤ (918110631675952567/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683499054517/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0037_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403877927703/200000000000 : ℝ) ≤ 4*Real.exp (505/4096 : ℝ)*Real.exp (-mu (radius 7 (253/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403877927703/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (253/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0037_exp_radius
  have hrNumeric : (491253466161/500000000000 : ℝ) ≤ Real.exp (-253/14336 : ℝ) ∧ Real.exp (-253/14336 : ℝ) ≤ (982506932323/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491253466161/500000000000 : ℝ) ≤ (radius 7 (253/2048 : ℝ)) ∧ (radius 7 (253/2048 : ℝ)) ≤ (982506932323/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (253/2048 : ℝ)) (491253466161/500000000000 : ℝ) (982506932323/1000000000000 : ℝ) (46556503263/250000000000 : ℝ) (93113006529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (253/2048 : ℝ)) (491253466161/500000000000 : ℝ) (982506932323/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (253/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491253466161/500000000000 : ℝ) (982506932323/1000000000000 : ℝ) (991253466161/1000000000000 : ℝ) (495626733081/500000000000 : ℝ) (991214876967/1000000000000 : ℝ) (991214876969/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (253/2048 : ℝ)) 1 (991253466161/1000000000000 : ℝ) (495626733081/500000000000 : ℝ) (991214876967/1000000000000 : ℝ) (991214876969/1000000000000 : ℝ) (247808542891/250000000000 : ℝ) (495617085783/500000000000 : ℝ) (61952135711/62500000000 : ℝ) (495617085689/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (253/2048 : ℝ)) 2 (247808542891/250000000000 : ℝ) (495617085783/500000000000 : ℝ) (61952135711/62500000000 : ℝ) (495617085689/500000000000 : ℝ) (99123417147/100000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (253/2048 : ℝ)) 3 (99123417147/100000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (253/2048 : ℝ)) 4 (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (253/2048 : ℝ)) 5 (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (253/2048 : ℝ)) 6 (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (253/2048 : ℝ)) 7 (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (253/2048 : ℝ))) (46556503263/250000000000 : ℝ) (93113006529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46556503263/250000000000 : ℝ) (93113006529/500000000000 : ℝ) (296556503263/500000000000 : ℝ) (593113006529/1000000000000 : ℝ) (215769560557/500000000000 : ℝ) (215769560561/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 1 (296556503263/500000000000 : ℝ) (593113006529/1000000000000 : ℝ) (215769560557/500000000000 : ℝ) (215769560561/500000000000 : ℝ) (25616303191/50000000000 : ℝ) (256163031913/500000000000 : ℝ) (252958230523/500000000000 : ℝ) (505916461053/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 2 (25616303191/50000000000 : ℝ) (256163031913/500000000000 : ℝ) (252958230523/500000000000 : ℝ) (505916461053/1000000000000 : ℝ) (509121262433/1000000000000 : ℝ) (12728031561/25000000000 : ℝ) (127277793897/250000000000 : ℝ) (127277793899/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 3 (509121262433/1000000000000 : ℝ) (12728031561/25000000000 : ℝ) (127277793897/250000000000 : ℝ) (127277793899/250000000000 : ℝ) (50911621901/100000000000 : ℝ) (254558109509/500000000000 : ℝ) (101823243797/200000000000 : ℝ) (254558109497/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 4 (50911621901/100000000000 : ℝ) (254558109509/500000000000 : ℝ) (101823243797/200000000000 : ℝ) (254558109497/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 5 (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 6 (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (253/2048 : ℝ))) 7 (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (253/2048 : ℝ)) hmem 8 (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (253/2048 : ℝ))) hcmem 8 (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (253/2048 : ℝ)) (991234171469/1000000000000 : ℝ) (61952135717/62500000000 : ℝ) (509116218997/1000000000000 : ℝ) (254558109503/500000000000 : ℝ) (6454320561/8000000000 : ℝ) (403395035071/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0037_exp_lower
  have heNumeric : (403877927703/200000000000 : ℝ)/4 ≤ Real.exp (-683499054517/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403877927703/200000000000 : ℝ)/4 ≤ Real.exp ((505/4096 : ℝ)-(403395035071/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (505/4096 : ℝ) (253/2048 : ℝ) (403395035071/500000000000 : ℝ) (403877927703/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0038; no trusted numerical premise.
theorem cover7_leaf0038_exp_radius : (498896048212859419/500000000000000000 : ℝ) ≤ Real.exp ((-507/28672 : ℝ)/8) ∧ Real.exp ((-507/28672 : ℝ)/8) ≤ (997792096425718839/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-507/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0038_exp_lower : (918108754292659459/1000000000000000000 : ℝ) ≤ Real.exp ((-683515413201/1000000000000 : ℝ)/8) ∧ Real.exp ((-683515413201/1000000000000 : ℝ)/8) ≤ (45905437714632973/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683515413201/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0038_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504839151057/250000000000 : ℝ) ≤ 4*Real.exp (253/2048 : ℝ)*Real.exp (-mu (radius 7 (507/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (504839151057/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (507/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0038_exp_radius
  have hrNumeric : (491236332899/500000000000 : ℝ) ≤ Real.exp (-507/28672 : ℝ) ∧ Real.exp (-507/28672 : ℝ) ≤ (982472665799/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491236332899/500000000000 : ℝ) ≤ (radius 7 (507/4096 : ℝ)) ∧ (radius 7 (507/4096 : ℝ)) ≤ (982472665799/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (507/4096 : ℝ)) (491236332899/500000000000 : ℝ) (982472665799/1000000000000 : ℝ) (186406708457/1000000000000 : ℝ) (186406708463/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (507/4096 : ℝ)) (491236332899/500000000000 : ℝ) (982472665799/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (507/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491236332899/500000000000 : ℝ) (982472665799/1000000000000 : ℝ) (991236332899/1000000000000 : ℝ) (9912363329/10000000000 : ℝ) (991197591703/1000000000000 : ℝ) (123899698963/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (507/4096 : ℝ)) 1 (991236332899/1000000000000 : ℝ) (9912363329/10000000000 : ℝ) (991197591703/1000000000000 : ℝ) (123899698963/125000000000 : ℝ) (991216962301/1000000000000 : ℝ) (495608481151/500000000000 : ℝ) (991216962111/1000000000000 : ℝ) (991216962113/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (507/4096 : ℝ)) 2 (991216962301/1000000000000 : ℝ) (495608481151/500000000000 : ℝ) (991216962111/1000000000000 : ℝ) (991216962113/1000000000000 : ℝ) (495608481103/500000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (507/4096 : ℝ)) 3 (495608481103/500000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (507/4096 : ℝ)) 4 (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (507/4096 : ℝ)) 5 (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (507/4096 : ℝ)) 6 (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (507/4096 : ℝ)) 7 (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (507/4096 : ℝ))) (186406708457/1000000000000 : ℝ) (186406708463/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (186406708457/1000000000000 : ℝ) (186406708463/1000000000000 : ℝ) (148300838557/250000000000 : ℝ) (74150419279/125000000000 : ℝ) (43174843191/100000000000 : ℝ) (215874215959/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 1 (148300838557/250000000000 : ℝ) (74150419279/125000000000 : ℝ) (43174843191/100000000000 : ℝ) (215874215959/500000000000 : ℝ) (512475893069/1000000000000 : ℝ) (20499035723/40000000000 : ℝ) (506077679799/1000000000000 : ℝ) (506077679807/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 2 (512475893069/1000000000000 : ℝ) (20499035723/40000000000 : ℝ) (506077679799/1000000000000 : ℝ) (506077679807/1000000000000 : ℝ) (254638393217/500000000000 : ℝ) (509276786441/1000000000000 : ℝ) (20370669539/40000000000 : ℝ) (509266738483/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 3 (254638393217/500000000000 : ℝ) (509276786441/1000000000000 : ℝ) (20370669539/40000000000 : ℝ) (509266738483/1000000000000 : ℝ) (254635881227/500000000000 : ℝ) (254635881231/500000000000 : ℝ) (509271762429/1000000000000 : ℝ) (254635881219/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 4 (254635881227/500000000000 : ℝ) (254635881231/500000000000 : ℝ) (509271762429/1000000000000 : ℝ) (254635881219/500000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 5 (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 6 (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (507/4096 : ℝ))) 7 (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (507/4096 : ℝ)) hmem 8 (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (507/4096 : ℝ))) hcmem 8 (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (507/4096 : ℝ)) (198243392441/200000000000 : ℝ) (30975530069/31250000000 : ℝ) (509271762441/1000000000000 : ℝ) (10185435249/20000000000 : ℝ) (403525284717/500000000000 : ℝ) (807050569451/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0038_exp_lower
  have heNumeric : (504839151057/250000000000 : ℝ)/4 ≤ Real.exp (-683515413201/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504839151057/250000000000 : ℝ)/4 ≤ Real.exp ((253/2048 : ℝ)-(807050569451/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (253/2048 : ℝ) (507/4096 : ℝ) (807050569451/1000000000000 : ℝ) (504839151057/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0039; no trusted numerical premise.
theorem cover7_leaf0039_exp_radius : (199557549281375793/200000000000000000 : ℝ) ≤ Real.exp ((-127/7168 : ℝ)/8) ∧ Real.exp ((-127/7168 : ℝ)/8) ≤ (498893873203439483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-127/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0039_exp_lower : (918106916566701211/1000000000000000000 : ℝ) ≤ Real.exp ((-683531426361/1000000000000 : ℝ)/8) ∧ Real.exp ((-683531426361/1000000000000 : ℝ)/8) ≤ (229526729141675303/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683531426361/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0039_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009662134103/500000000000 : ℝ) ≤ 4*Real.exp (507/4096 : ℝ)*Real.exp (-mu (radius 7 (127/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009662134103/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (127/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0039_exp_radius
  have hrNumeric : (245609600117/250000000000 : ℝ) ≤ Real.exp (-127/7168 : ℝ) ∧ Real.exp (-127/7168 : ℝ) ≤ (982438400469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245609600117/250000000000 : ℝ) ≤ (radius 7 (127/1024 : ℝ)) ∧ (radius 7 (127/1024 : ℝ)) ≤ (982438400469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (127/1024 : ℝ)) (245609600117/250000000000 : ℝ) (982438400469/1000000000000 : ℝ) (46646804073/250000000000 : ℝ) (186587216299/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (127/1024 : ℝ)) (245609600117/250000000000 : ℝ) (982438400469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (127/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245609600117/250000000000 : ℝ) (982438400469/1000000000000 : ℝ) (495609600117/500000000000 : ℝ) (198243840047/200000000000 : ℝ) (991180306739/1000000000000 : ℝ) (49559015337/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (127/1024 : ℝ)) 1 (495609600117/500000000000 : ℝ) (198243840047/200000000000 : ℝ) (991180306739/1000000000000 : ℝ) (49559015337/50000000000 : ℝ) (495599876743/500000000000 : ℝ) (61949984593/62500000000 : ℝ) (198239950659/200000000000 : ℝ) (991199753297/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (127/1024 : ℝ)) 2 (495599876743/500000000000 : ℝ) (61949984593/62500000000 : ℝ) (198239950659/200000000000 : ℝ) (991199753297/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (127/1024 : ℝ)) 3 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (127/1024 : ℝ)) 4 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (127/1024 : ℝ)) 5 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (127/1024 : ℝ)) 6 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (127/1024 : ℝ)) 7 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (127/1024 : ℝ))) (46646804073/250000000000 : ℝ) (186587216299/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46646804073/250000000000 : ℝ) (186587216299/1000000000000 : ℝ) (296646804073/500000000000 : ℝ) (11865872163/20000000000 : ℝ) (86391484833/200000000000 : ℝ) (215978712087/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 1 (296646804073/500000000000 : ℝ) (11865872163/20000000000 : ℝ) (86391484833/200000000000 : ℝ) (215978712087/500000000000 : ℝ) (102525103231/200000000000 : ℝ) (256312758081/500000000000 : ℝ) (101247731579/200000000000 : ℝ) (506238657903/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 2 (102525103231/200000000000 : ℝ) (256312758081/500000000000 : ℝ) (101247731579/200000000000 : ℝ) (506238657903/1000000000000 : ℝ) (20377283481/40000000000 : ℝ) (509432087033/1000000000000 : ℝ) (509422077751/1000000000000 : ℝ) (1591943993/3125000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 3 (20377283481/40000000000 : ℝ) (509432087033/1000000000000 : ℝ) (509422077751/1000000000000 : ℝ) (1591943993/3125000000 : ℝ) (127356770597/250000000000 : ℝ) (509427082397/1000000000000 : ℝ) (509427082363/1000000000000 : ℝ) (127356770593/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 4 (127356770597/250000000000 : ℝ) (509427082397/1000000000000 : ℝ) (509427082363/1000000000000 : ℝ) (127356770593/250000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 5 (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 6 (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (127/1024 : ℝ))) 7 (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (127/1024 : ℝ)) hmem 8 (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (127/1024 : ℝ))) hcmem 8 (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (127/1024 : ℝ)) (99119975339/100000000000 : ℝ) (991199753393/1000000000000 : ℝ) (4075416659/8000000000 : ℝ) (101885416477/200000000000 : ℝ) (807310723217/1000000000000 : ℝ) (201827680809/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0039_exp_lower
  have heNumeric : (1009662134103/500000000000 : ℝ)/4 ≤ Real.exp (-683531426361/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009662134103/500000000000 : ℝ)/4 ≤ Real.exp ((507/4096 : ℝ)-(201827680809/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (507/4096 : ℝ) (127/1024 : ℝ) (201827680809/250000000000 : ℝ) (1009662134103/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0040; no trusted numerical premise.
theorem cover7_leaf0040_exp_radius : (249445849101750907/250000000000000000 : ℝ) ≤ Real.exp ((-509/28672 : ℝ)/8) ∧ Real.exp ((-509/28672 : ℝ)/8) ≤ (997783396407003629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-509/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0040_exp_lower : (229526279590633489/250000000000000000 : ℝ) ≤ Real.exp ((-85443386897/125000000000 : ℝ)/8) ∧ Real.exp ((-85443386897/125000000000 : ℝ)/8) ≤ (918105118362533957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85443386897/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0040_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504823157009/250000000000 : ℝ) ≤ 4*Real.exp (127/1024 : ℝ)*Real.exp (-mu (radius 7 (509/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (504823157009/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (509/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0040_exp_radius
  have hrNumeric : (982404136333/1000000000000 : ℝ) ≤ Real.exp (-509/28672 : ℝ) ∧ Real.exp (-509/28672 : ℝ) ≤ (491202068167/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982404136333/1000000000000 : ℝ) ≤ (radius 7 (509/4096 : ℝ)) ∧ (radius 7 (509/4096 : ℝ)) ≤ (491202068167/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (509/4096 : ℝ)) (982404136333/1000000000000 : ℝ) (491202068167/500000000000 : ℝ) (93383768549/500000000000 : ℝ) (11672971069/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (509/4096 : ℝ)) (982404136333/1000000000000 : ℝ) (491202068167/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (509/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982404136333/1000000000000 : ℝ) (491202068167/500000000000 : ℝ) (495601034083/500000000000 : ℝ) (991202068167/1000000000000 : ℝ) (991163022077/1000000000000 : ℝ) (495581511039/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (509/4096 : ℝ)) 1 (495601034083/500000000000 : ℝ) (991202068167/1000000000000 : ℝ) (991163022077/1000000000000 : ℝ) (495581511039/500000000000 : ℝ) (991182545121/1000000000000 : ℝ) (991182545123/1000000000000 : ℝ) (991182544929/1000000000000 : ℝ) (991182544931/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (509/4096 : ℝ)) 2 (991182545121/1000000000000 : ℝ) (991182545123/1000000000000 : ℝ) (991182544929/1000000000000 : ℝ) (991182544931/1000000000000 : ℝ) (39647301801/40000000000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (509/4096 : ℝ)) 3 (39647301801/40000000000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (509/4096 : ℝ)) 4 (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (509/4096 : ℝ)) 5 (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (509/4096 : ℝ)) 6 (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (509/4096 : ℝ)) 7 (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (509/4096 : ℝ))) (93383768549/500000000000 : ℝ) (11672971069/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (93383768549/500000000000 : ℝ) (11672971069/62500000000 : ℝ) (593383768549/1000000000000 : ℝ) (74172971069/125000000000 : ℝ) (54020762371/125000000000 : ℝ) (13505190593/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 1 (593383768549/1000000000000 : ℝ) (74172971069/125000000000 : ℝ) (54020762371/125000000000 : ℝ) (13505190593/31250000000 : ℝ) (256387466879/500000000000 : ℝ) (128193733441/250000000000 : ℝ) (506399396173/1000000000000 : ℝ) (25319969809/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 2 (256387466879/500000000000 : ℝ) (128193733441/250000000000 : ℝ) (506399396173/1000000000000 : ℝ) (25319969809/50000000000 : ℝ) (101917432993/200000000000 : ℝ) (127396791243/250000000000 : ℝ) (509577194179/1000000000000 : ℝ) (254788597093/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 3 (101917432993/200000000000 : ℝ) (127396791243/250000000000 : ℝ) (509577194179/1000000000000 : ℝ) (254788597093/500000000000 : ℝ) (127395544893/250000000000 : ℝ) (509582179579/1000000000000 : ℝ) (509582179547/1000000000000 : ℝ) (101916435911/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 4 (127395544893/250000000000 : ℝ) (509582179579/1000000000000 : ℝ) (509582179547/1000000000000 : ℝ) (101916435911/200000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 5 (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 6 (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (509/4096 : ℝ))) 7 (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (509/4096 : ℝ)) hmem 8 (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (509/4096 : ℝ))) hcmem 8 (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (509/4096 : ℝ)) (7743613633/7812500000 : ℝ) (991182545027/1000000000000 : ℝ) (509582179559/1000000000000 : ℝ) (509582179567/1000000000000 : ℝ) (40378526633/50000000000 : ℝ) (201892633169/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0040_exp_lower
  have heNumeric : (504823157009/250000000000 : ℝ)/4 ≤ Real.exp (-85443386897/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504823157009/250000000000 : ℝ)/4 ≤ Real.exp ((127/1024 : ℝ)-(201892633169/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (127/1024 : ℝ) (509/4096 : ℝ) (201892633169/250000000000 : ℝ) (504823157009/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0041; no trusted numerical premise.
theorem cover7_leaf0041_exp_radius : (124722380803261593/125000000000000000 : ℝ) ≤ Real.exp ((-255/14336 : ℝ)/8) ∧ Real.exp ((-255/14336 : ℝ)/8) ≤ (199555809285218549/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-255/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0041_exp_lower : (918103359544160953/1000000000000000000 : ℝ) ≤ Real.exp ((-683562420829/1000000000000 : ℝ)/8) ∧ Real.exp ((-683562420829/1000000000000 : ℝ)/8) ≤ (459051679772080477/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683562420829/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0041_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403852336259/200000000000 : ℝ) ≤ 4*Real.exp (509/4096 : ℝ)*Real.exp (-mu (radius 7 (255/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403852336259/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (255/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0041_exp_radius
  have hrNumeric : (491184936697/500000000000 : ℝ) ≤ Real.exp (-255/14336 : ℝ) ∧ Real.exp (-255/14336 : ℝ) ≤ (196473974679/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491184936697/500000000000 : ℝ) ≤ (radius 7 (255/2048 : ℝ)) ∧ (radius 7 (255/2048 : ℝ)) ≤ (196473974679/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (255/2048 : ℝ)) (491184936697/500000000000 : ℝ) (196473974679/200000000000 : ℝ) (18694767141/100000000000 : ℝ) (23368458927/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (255/2048 : ℝ)) (491184936697/500000000000 : ℝ) (196473974679/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (255/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491184936697/500000000000 : ℝ) (196473974679/200000000000 : ℝ) (991184936697/1000000000000 : ℝ) (495592468349/500000000000 : ℝ) (247786434429/250000000000 : ℝ) (495572868859/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (255/2048 : ℝ)) 1 (991184936697/1000000000000 : ℝ) (495592468349/500000000000 : ℝ) (247786434429/250000000000 : ℝ) (495572868859/500000000000 : ℝ) (495582668603/500000000000 : ℝ) (123895667151/125000000000 : ℝ) (247791334253/250000000000 : ℝ) (198233067403/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (255/2048 : ℝ)) 2 (495582668603/500000000000 : ℝ) (123895667151/125000000000 : ℝ) (247791334253/250000000000 : ℝ) (198233067403/200000000000 : ℝ) (991165337109/1000000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (255/2048 : ℝ)) 3 (991165337109/1000000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (255/2048 : ℝ)) 4 (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (255/2048 : ℝ)) 5 (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (255/2048 : ℝ)) 6 (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (255/2048 : ℝ)) 7 (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (255/2048 : ℝ))) (18694767141/100000000000 : ℝ) (23368458927/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18694767141/100000000000 : ℝ) (23368458927/125000000000 : ℝ) (118694767141/200000000000 : ℝ) (148368458927/250000000000 : ℝ) (432374457397/1000000000000 : ℝ) (86474891481/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 1 (118694767141/200000000000 : ℝ) (148368458927/250000000000 : ℝ) (432374457397/1000000000000 : ℝ) (86474891481/200000000000 : ℝ) (512924146551/1000000000000 : ℝ) (512924146557/1000000000000 : ℝ) (506559895463/1000000000000 : ℝ) (50655989547/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 2 (512924146551/1000000000000 : ℝ) (512924146557/1000000000000 : ℝ) (506559895463/1000000000000 : ℝ) (50655989547/100000000000 : ℝ) (509742021007/1000000000000 : ℝ) (254871010507/500000000000 : ℝ) (50973208851/100000000000 : ℝ) (254866044259/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 3 (509742021007/1000000000000 : ℝ) (254871010507/500000000000 : ℝ) (50973208851/100000000000 : ℝ) (254866044259/500000000000 : ℝ) (254868527379/500000000000 : ℝ) (254868527383/500000000000 : ℝ) (254868527367/500000000000 : ℝ) (254868527371/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 4 (254868527379/500000000000 : ℝ) (254868527383/500000000000 : ℝ) (254868527367/500000000000 : ℝ) (254868527371/500000000000 : ℝ) (254868527373/500000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 5 (254868527373/500000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 6 (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (255/2048 : ℝ))) 7 (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (255/2048 : ℝ)) hmem 8 (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (255/2048 : ℝ))) hcmem 8 (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (255/2048 : ℝ)) (247791334277/250000000000 : ℝ) (123895667139/125000000000 : ℝ) (101947410949/200000000000 : ℝ) (254868527377/500000000000 : ℝ) (100978749867/125000000000 : ℝ) (403914999477/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0041_exp_lower
  have heNumeric : (403852336259/200000000000 : ℝ)/4 ≤ Real.exp (-683562420829/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403852336259/200000000000 : ℝ)/4 ≤ Real.exp ((509/4096 : ℝ)-(403914999477/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (509/4096 : ℝ) (255/2048 : ℝ) (403914999477/500000000000 : ℝ) (403852336259/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0042; no trusted numerical premise.
theorem cover7_leaf0042_exp_radius : (99777469646414623/100000000000000000 : ℝ) ≤ Real.exp ((-73/4096 : ℝ)/8) ∧ Real.exp ((-73/4096 : ℝ)/8) ≤ (997774696464146231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-73/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0042_exp_lower : (229525409993725751/250000000000000000 : ℝ) ≤ Real.exp ((-683577404509/1000000000000 : ℝ)/8) ∧ Real.exp ((-683577404509/1000000000000 : ℝ)/8) ≤ (183620327994980601/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683577404509/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0042_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019231425551/1000000000000 : ℝ) ≤ 4*Real.exp (255/2048 : ℝ)*Real.exp (-mu (radius 7 (511/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019231425551/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (511/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0042_exp_radius
  have hrNumeric : (982335611649/1000000000000 : ℝ) ≤ Real.exp (-73/4096 : ℝ) ∧ Real.exp (-73/4096 : ℝ) ≤ (19646712233/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982335611649/1000000000000 : ℝ) ≤ (radius 7 (511/4096 : ℝ)) ∧ (radius 7 (511/4096 : ℝ)) ≤ (19646712233/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (511/4096 : ℝ)) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (511/4096 : ℝ)) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (511/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) (7743498483/7812500000 : ℝ) (39646712233/40000000000 : ℝ) (991128453657/1000000000000 : ℝ) (495564226829/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (511/4096 : ℝ)) 1 (7743498483/7812500000 : ℝ) (39646712233/40000000000 : ℝ) (991128453657/1000000000000 : ℝ) (495564226829/500000000000 : ℝ) (49557406487/50000000000 : ℝ) (495574064871/500000000000 : ℝ) (198229625909/200000000000 : ℝ) (991148129547/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (511/4096 : ℝ)) 2 (49557406487/50000000000 : ℝ) (495574064871/500000000000 : ℝ) (198229625909/200000000000 : ℝ) (991148129547/1000000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (511/4096 : ℝ)) 3 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (511/4096 : ℝ)) 4 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (511/4096 : ℝ)) 5 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (511/4096 : ℝ)) 6 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (511/4096 : ℝ)) 7 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (511/4096 : ℝ))) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ) (593563809889/1000000000000 : ℝ) (593563809893/1000000000000 : ℝ) (216291250273/500000000000 : ℝ) (216291250277/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 1 (593563809889/1000000000000 : ℝ) (593563809893/1000000000000 : ℝ) (216291250273/500000000000 : ℝ) (216291250277/500000000000 : ℝ) (513073155217/1000000000000 : ℝ) (64134144403/125000000000 : ℝ) (50672015661/100000000000 : ℝ) (506720156617/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 2 (513073155217/1000000000000 : ℝ) (64134144403/125000000000 : ℝ) (50672015661/100000000000 : ℝ) (506720156617/1000000000000 : ℝ) (509896655913/1000000000000 : ℝ) (509896655921/1000000000000 : ℝ) (50988676151/100000000000 : ℝ) (254943380759/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 3 (509896655913/1000000000000 : ℝ) (509896655921/1000000000000 : ℝ) (50988676151/100000000000 : ℝ) (254943380759/500000000000 : ℝ) (509891708711/1000000000000 : ℝ) (6373646359/12500000000 : ℝ) (509891708687/1000000000000 : ℝ) (63736463587/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 4 (509891708711/1000000000000 : ℝ) (6373646359/12500000000 : ℝ) (509891708687/1000000000000 : ℝ) (63736463587/125000000000 : ℝ) (509891708699/1000000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 5 (509891708699/1000000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 6 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (511/4096 : ℝ))) 7 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (511/4096 : ℝ)) hmem 8 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (511/4096 : ℝ))) hcmem 8 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (511/4096 : ℝ)) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (20202228081/25000000000 : ℝ) (808089123259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0042_exp_lower
  have heNumeric : (2019231425551/1000000000000 : ℝ)/4 ≤ Real.exp (-683577404509/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019231425551/1000000000000 : ℝ)/4 ≤ Real.exp ((255/2048 : ℝ)-(808089123259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (255/2048 : ℝ) (511/4096 : ℝ) (808089123259/1000000000000 : ℝ) (2019231425551/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0043; no trusted numerical premise.
theorem cover7_leaf0043_exp_radius : (249442586630291001/250000000000000000 : ℝ) ≤ Real.exp ((-1/56 : ℝ)/8) ∧ Real.exp ((-1/56 : ℝ)/8) ≤ (199554069304232801/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/56 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0043_exp_lower : (229524989880267701/250000000000000000 : ℝ) ≤ Real.exp ((-683592047379/1000000000000 : ℝ)/8) ∧ Real.exp ((-683592047379/1000000000000 : ℝ)/8) ≤ (183619991904214161/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683592047379/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0043_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252400232303/125000000000 : ℝ) ≤ 4*Real.exp (511/4096 : ℝ)*Real.exp (-mu (radius 7 (1/8 : ℝ))) ∧ (2019/1000 : ℝ) < (252400232303/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/8 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0043_exp_radius
  have hrNumeric : (982301351099/1000000000000 : ℝ) ≤ Real.exp (-1/56 : ℝ) ∧ Real.exp (-1/56 : ℝ) ≤ (9823013511/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982301351099/1000000000000 : ℝ) ≤ (radius 7 (1/8 : ℝ)) ∧ (radius 7 (1/8 : ℝ)) ≤ (9823013511/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/8 : ℝ)) (982301351099/1000000000000 : ℝ) (9823013511/10000000000 : ℝ) (37461476547/200000000000 : ℝ) (187307382741/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/8 : ℝ)) (982301351099/1000000000000 : ℝ) (9823013511/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/8 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982301351099/1000000000000 : ℝ) (9823013511/10000000000 : ℝ) (991150675549/1000000000000 : ℝ) (19823013511/20000000000 : ℝ) (991111169899/1000000000000 : ℝ) (9911111699/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/8 : ℝ)) 1 (991150675549/1000000000000 : ℝ) (19823013511/20000000000 : ℝ) (991111169899/1000000000000 : ℝ) (9911111699/10000000000 : ℝ) (247782730681/250000000000 : ℝ) (39645236909/40000000000 : ℝ) (991130922527/1000000000000 : ℝ) (991130922529/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/8 : ℝ)) 2 (247782730681/250000000000 : ℝ) (39645236909/40000000000 : ℝ) (991130922527/1000000000000 : ℝ) (991130922529/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/8 : ℝ)) 3 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/8 : ℝ)) 4 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/8 : ℝ)) 5 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/8 : ℝ)) 6 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/8 : ℝ)) 7 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/8 : ℝ))) (37461476547/200000000000 : ℝ) (187307382741/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37461476547/200000000000 : ℝ) (187307382741/1000000000000 : ℝ) (593653691367/1000000000000 : ℝ) (593653691371/1000000000000 : ℝ) (432790229481/1000000000000 : ℝ) (432790229489/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 1 (593653691367/1000000000000 : ℝ) (593653691371/1000000000000 : ℝ) (432790229481/1000000000000 : ℝ) (432790229489/1000000000000 : ℝ) (64152745053/125000000000 : ℝ) (51322196043/100000000000 : ℝ) (126720045109/250000000000 : ℝ) (506880180443/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 2 (64152745053/125000000000 : ℝ) (51322196043/100000000000 : ℝ) (126720045109/250000000000 : ℝ) (506880180443/1000000000000 : ℝ) (51005107043/100000000000 : ℝ) (510051070437/1000000000000 : ℝ) (255020606963/500000000000 : ℝ) (510041213933/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 3 (51005107043/100000000000 : ℝ) (510051070437/1000000000000 : ℝ) (255020606963/500000000000 : ℝ) (510041213933/1000000000000 : ℝ) (255023071089/500000000000 : ℝ) (102009228437/200000000000 : ℝ) (255023071077/500000000000 : ℝ) (255023071081/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 4 (255023071089/500000000000 : ℝ) (102009228437/200000000000 : ℝ) (255023071077/500000000000 : ℝ) (255023071081/500000000000 : ℝ) (255023071083/500000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 5 (255023071083/500000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 6 (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/8 : ℝ))) 7 (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/8 : ℝ)) hmem 8 (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/8 : ℝ))) hcmem 8 (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/8 : ℝ)) (7929047381/8000000000 : ℝ) (991130922627/1000000000000 : ℝ) (102009228433/200000000000 : ℝ) (255023071087/500000000000 : ℝ) (808347906737/1000000000000 : ℝ) (404173953377/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0043_exp_lower
  have heNumeric : (252400232303/125000000000 : ℝ)/4 ≤ Real.exp (-683592047379/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252400232303/125000000000 : ℝ)/4 ≤ Real.exp ((511/4096 : ℝ)-(404173953377/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (511/4096 : ℝ) (1/8 : ℝ) (404173953377/500000000000 : ℝ) (252400232303/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0044; no trusted numerical premise.
theorem cover7_leaf0044_exp_radius : (997765996597145983/1000000000000000000 : ℝ) ≤ Real.exp ((-513/28672 : ℝ)/8) ∧ Real.exp ((-513/28672 : ℝ)/8) ≤ (7795046848415203/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-513/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0044_exp_lower : (114762289756050903/125000000000000000 : ℝ) ≤ Real.exp ((-683606350607/1000000000000 : ℝ)/8) ∧ Real.exp ((-683606350607/1000000000000 : ℝ)/8) ≤ (36723932721936289/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683606350607/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0044_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009586488763/500000000000 : ℝ) ≤ 4*Real.exp (1/8 : ℝ)*Real.exp (-mu (radius 7 (513/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009586488763/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (513/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0044_exp_radius
  have hrNumeric : (30695846617/31250000000 : ℝ) ≤ Real.exp (-513/28672 : ℝ) ∧ Real.exp (-513/28672 : ℝ) ≤ (196453418349/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30695846617/31250000000 : ℝ) ≤ (radius 7 (513/4096 : ℝ)) ∧ (radius 7 (513/4096 : ℝ)) ≤ (196453418349/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (513/4096 : ℝ)) (30695846617/31250000000 : ℝ) (196453418349/200000000000 : ℝ) (46871740203/250000000000 : ℝ) (187486960819/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (513/4096 : ℝ)) (30695846617/31250000000 : ℝ) (196453418349/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (513/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30695846617/31250000000 : ℝ) (196453418349/200000000000 : ℝ) (61945846617/62500000000 : ℝ) (991133545873/1000000000000 : ℝ) (495546943221/500000000000 : ℝ) (247773471611/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (513/4096 : ℝ)) 1 (61945846617/62500000000 : ℝ) (991133545873/1000000000000 : ℝ) (495546943221/500000000000 : ℝ) (247773471611/250000000000 : ℝ) (991113716157/1000000000000 : ℝ) (991113716159/1000000000000 : ℝ) (495556857979/500000000000 : ℝ) (991113715961/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (513/4096 : ℝ)) 2 (991113716157/1000000000000 : ℝ) (991113716159/1000000000000 : ℝ) (495556857979/500000000000 : ℝ) (991113715961/1000000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (513/4096 : ℝ)) 3 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (513/4096 : ℝ)) 4 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (513/4096 : ℝ)) 5 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (513/4096 : ℝ)) 6 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (513/4096 : ℝ)) 7 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (513/4096 : ℝ))) (46871740203/250000000000 : ℝ) (187486960819/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46871740203/250000000000 : ℝ) (187486960819/1000000000000 : ℝ) (296871740203/500000000000 : ℝ) (59374348041/100000000000 : ℝ) (432997645273/1000000000000 : ℝ) (216498822641/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 1 (296871740203/500000000000 : ℝ) (59374348041/100000000000 : ℝ) (432997645273/1000000000000 : ℝ) (216498822641/500000000000 : ℝ) (513370562839/1000000000000 : ℝ) (256685281423/500000000000 : ℝ) (101407993553/200000000000 : ℝ) (507039967773/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 2 (513370562839/1000000000000 : ℝ) (256685281423/500000000000 : ℝ) (101407993553/200000000000 : ℝ) (507039967773/1000000000000 : ℝ) (255102632651/500000000000 : ℝ) (51020526531/100000000000 : ℝ) (510195446503/1000000000000 : ℝ) (31887215407/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 3 (255102632651/500000000000 : ℝ) (51020526531/100000000000 : ℝ) (510195446503/1000000000000 : ℝ) (31887215407/62500000000 : ℝ) (255100177951/500000000000 : ℝ) (510200355911/1000000000000 : ℝ) (255100177939/500000000000 : ℝ) (31887522243/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 4 (255100177951/500000000000 : ℝ) (510200355911/1000000000000 : ℝ) (255100177939/500000000000 : ℝ) (31887522243/62500000000 : ℝ) (51020035589/100000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 5 (51020035589/100000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 6 (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (513/4096 : ℝ))) 7 (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (513/4096 : ℝ)) hmem 8 (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (513/4096 : ℝ))) hcmem 8 (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (513/4096 : ℝ)) (991113716057/1000000000000 : ℝ) (49555685803/50000000000 : ℝ) (510200355889/1000000000000 : ℝ) (5102003559/10000000000 : ℝ) (404303175293/500000000000 : ℝ) (808606350607/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0044_exp_lower
  have heNumeric : (1009586488763/500000000000 : ℝ)/4 ≤ Real.exp (-683606350607/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009586488763/500000000000 : ℝ)/4 ≤ Real.exp ((1/8 : ℝ)-(808606350607/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1/8 : ℝ) (513/4096 : ℝ) (808606350607/1000000000000 : ℝ) (1009586488763/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0045; no trusted numerical premise.
theorem cover7_leaf0045_exp_radius : (199552329338418417/200000000000000000 : ℝ) ≤ Real.exp ((-257/14336 : ℝ)/8) ∧ Real.exp ((-257/14336 : ℝ)/8) ≤ (498880823346046043/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-257/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0045_exp_lower : (918096715424038217/1000000000000000000 : ℝ) ≤ Real.exp ((-683620315349/1000000000000 : ℝ)/8) ∧ Real.exp ((-683620315349/1000000000000 : ℝ)/8) ≤ (459048357712019109/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683620315349/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0045_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019144780493/1000000000000 : ℝ) ≤ 4*Real.exp (513/4096 : ℝ)*Real.exp (-mu (radius 7 (257/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019144780493/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (257/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0045_exp_radius
  have hrNumeric : (61389552099/62500000000 : ℝ) ≤ Real.exp (-257/14336 : ℝ) ∧ Real.exp (-257/14336 : ℝ) ≤ (196446566717/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61389552099/62500000000 : ℝ) ≤ (radius 7 (257/2048 : ℝ)) ∧ (radius 7 (257/2048 : ℝ)) ≤ (196446566717/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (257/2048 : ℝ)) (61389552099/62500000000 : ℝ) (196446566717/200000000000 : ℝ) (187666354543/1000000000000 : ℝ) (187666354549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (257/2048 : ℝ)) (61389552099/62500000000 : ℝ) (196446566717/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (257/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61389552099/62500000000 : ℝ) (196446566717/200000000000 : ℝ) (123889552099/125000000000 : ℝ) (991116416793/1000000000000 : ℝ) (991076603287/1000000000000 : ℝ) (991076603289/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (257/2048 : ℝ)) 1 (123889552099/125000000000 : ℝ) (991116416793/1000000000000 : ℝ) (991076603287/1000000000000 : ℝ) (991076603289/1000000000000 : ℝ) (991096510039/1000000000000 : ℝ) (991096510041/1000000000000 : ℝ) (991096509839/1000000000000 : ℝ) (495548254921/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (257/2048 : ℝ)) 2 (991096510039/1000000000000 : ℝ) (991096510041/1000000000000 : ℝ) (991096509839/1000000000000 : ℝ) (495548254921/500000000000 : ℝ) (991096509939/1000000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (257/2048 : ℝ)) 3 (991096509939/1000000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (257/2048 : ℝ)) 4 (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (257/2048 : ℝ)) 5 (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (257/2048 : ℝ)) 6 (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (257/2048 : ℝ)) 7 (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (257/2048 : ℝ))) (187666354543/1000000000000 : ℝ) (187666354549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (187666354543/1000000000000 : ℝ) (187666354549/1000000000000 : ℝ) (593833177271/1000000000000 : ℝ) (23753327091/40000000000 : ℝ) (54150593623/125000000000 : ℝ) (6768824203/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 1 (593833177271/1000000000000 : ℝ) (23753327091/40000000000 : ℝ) (54150593623/125000000000 : ℝ) (6768824203/15625000000 : ℝ) (513518963127/1000000000000 : ℝ) (256759481567/500000000000 : ℝ) (253599759709/500000000000 : ℝ) (20287980777/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 2 (513518963127/1000000000000 : ℝ) (256759481567/500000000000 : ℝ) (253599759709/500000000000 : ℝ) (20287980777/40000000000 : ℝ) (63794905159/125000000000 : ℝ) (1594872629/3125000000 : ℝ) (127587364997/250000000000 : ℝ) (127587364999/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 3 (63794905159/125000000000 : ℝ) (1594872629/3125000000 : ℝ) (127587364997/250000000000 : ℝ) (127587364999/250000000000 : ℝ) (51035435063/100000000000 : ℝ) (255177175319/500000000000 : ℝ) (255177175303/500000000000 : ℝ) (102070870123/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 4 (51035435063/100000000000 : ℝ) (255177175319/500000000000 : ℝ) (255177175303/500000000000 : ℝ) (102070870123/200000000000 : ℝ) (255177175309/500000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 5 (255177175309/500000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 6 (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (257/2048 : ℝ))) 7 (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (257/2048 : ℝ)) hmem 8 (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (257/2048 : ℝ))) hcmem 8 (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (257/2048 : ℝ)) (495548254969/500000000000 : ℝ) (495548254971/500000000000 : ℝ) (510354350617/1000000000000 : ℝ) (510354350627/1000000000000 : ℝ) (404432227977/500000000000 : ℝ) (404432227987/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0045_exp_lower
  have heNumeric : (2019144780493/1000000000000 : ℝ)/4 ≤ Real.exp (-683620315349/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019144780493/1000000000000 : ℝ)/4 ≤ Real.exp ((513/4096 : ℝ)-(404432227987/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (513/4096 : ℝ) (257/2048 : ℝ) (404432227987/500000000000 : ℝ) (2019144780493/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0046; no trusted numerical premise.
theorem cover7_leaf0046_exp_radius : (498878648403001113/500000000000000000 : ℝ) ≤ Real.exp ((-515/28672 : ℝ)/8) ∧ Real.exp ((-515/28672 : ℝ)/8) ≤ (997757296806002227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-515/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0046_exp_lower : (183619030303042073/200000000000000000 : ℝ) ≤ Real.exp ((-17090848569/25000000000 : ℝ)/8) ∧ Real.exp ((-17090848569/25000000000 : ℝ)/8) ≤ (459047575757605183/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17090848569/25000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0046_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403823452993/200000000000 : ℝ) ≤ 4*Real.exp (257/2048 : ℝ)*Real.exp (-mu (radius 7 (515/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (403823452993/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (515/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0046_exp_radius
  have hrNumeric : (982198576619/1000000000000 : ℝ) ≤ Real.exp (-515/28672 : ℝ) ∧ Real.exp (-515/28672 : ℝ) ≤ (49109928831/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982198576619/1000000000000 : ℝ) ≤ (radius 7 (515/4096 : ℝ)) ∧ (radius 7 (515/4096 : ℝ)) ≤ (49109928831/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (515/4096 : ℝ)) (982198576619/1000000000000 : ℝ) (49109928831/50000000000 : ℝ) (37569112891/200000000000 : ℝ) (187845564461/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (515/4096 : ℝ)) (982198576619/1000000000000 : ℝ) (49109928831/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (515/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982198576619/1000000000000 : ℝ) (49109928831/50000000000 : ℝ) (991099288309/1000000000000 : ℝ) (99109928831/100000000000 : ℝ) (991059320433/1000000000000 : ℝ) (198211864087/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (515/4096 : ℝ)) 1 (991099288309/1000000000000 : ℝ) (99109928831/100000000000 : ℝ) (991059320433/1000000000000 : ℝ) (198211864087/200000000000 : ℝ) (991079304371/1000000000000 : ℝ) (991079304373/1000000000000 : ℝ) (991079304169/1000000000000 : ℝ) (247769826043/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (515/4096 : ℝ)) 2 (991079304371/1000000000000 : ℝ) (991079304373/1000000000000 : ℝ) (991079304169/1000000000000 : ℝ) (247769826043/250000000000 : ℝ) (99107930427/100000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (515/4096 : ℝ)) 3 (99107930427/100000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (515/4096 : ℝ)) 4 (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (515/4096 : ℝ)) 5 (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (515/4096 : ℝ)) 6 (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (515/4096 : ℝ)) 7 (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (515/4096 : ℝ))) (37569112891/200000000000 : ℝ) (187845564461/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37569112891/200000000000 : ℝ) (187845564461/1000000000000 : ℝ) (593922782227/1000000000000 : ℝ) (593922782231/1000000000000 : ℝ) (54176442709/125000000000 : ℝ) (5417644271/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 1 (593922782227/1000000000000 : ℝ) (593922782231/1000000000000 : ℝ) (54176442709/125000000000 : ℝ) (5417644271/12500000000 : ℝ) (513667161949/1000000000000 : ℝ) (128416790489/250000000000 : ℝ) (31709927263/62500000000 : ℝ) (63419854527/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 2 (513667161949/1000000000000 : ℝ) (128416790489/250000000000 : ℝ) (31709927263/62500000000 : ℝ) (63419854527/125000000000 : ℝ) (255256499539/500000000000 : ℝ) (255256499543/500000000000 : ℝ) (127625813779/250000000000 : ℝ) (4084026041/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 3 (255256499539/500000000000 : ℝ) (255256499543/500000000000 : ℝ) (127625813779/250000000000 : ℝ) (4084026041/8000000000 : ℝ) (510508127097/1000000000000 : ℝ) (255254063553/500000000000 : ℝ) (510508127073/1000000000000 : ℝ) (510508127083/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 4 (510508127097/1000000000000 : ℝ) (255254063553/500000000000 : ℝ) (510508127073/1000000000000 : ℝ) (510508127083/1000000000000 : ℝ) (102101625417/200000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 5 (102101625417/200000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 6 (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (515/4096 : ℝ))) 7 (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (515/4096 : ℝ)) hmem 8 (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (515/4096 : ℝ))) hcmem 8 (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (515/4096 : ℝ)) (991079304269/1000000000000 : ℝ) (991079304273/1000000000000 : ℝ) (127627031771/250000000000 : ℝ) (102101625419/200000000000 : ℝ) (202280555997/250000000000 : ℝ) (80912222401/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0046_exp_lower
  have heNumeric : (403823452993/200000000000 : ℝ)/4 ≤ Real.exp (-17090848569/25000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403823452993/200000000000 : ℝ)/4 ≤ Real.exp ((257/2048 : ℝ)-(80912222401/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (257/2048 : ℝ) (515/4096 : ℝ) (80912222401/100000000000 : ℝ) (403823452993/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0047; no trusted numerical premise.
theorem cover7_leaf0047_exp_radius : (249438236734719081/250000000000000000 : ℝ) ≤ Real.exp ((-129/7168 : ℝ)/8) ∧ Real.exp ((-129/7168 : ℝ)/8) ≤ (39910117877555053/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-129/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0047_exp_lower : (459046813095219221/500000000000000000 : ℝ) ≤ Real.exp ((-10681988031/15625000000 : ℝ)/8) ∧ Real.exp ((-10681988031/15625000000 : ℝ)/8) ≤ (918093626190438443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10681988031/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0047_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019090428603/1000000000000 : ℝ) ≤ 4*Real.exp (515/4096 : ℝ)*Real.exp (-mu (radius 7 (129/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019090428603/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (129/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0047_exp_radius
  have hrNumeric : (982164320849/1000000000000 : ℝ) ≤ Real.exp (-129/7168 : ℝ) ∧ Real.exp (-129/7168 : ℝ) ≤ (19643286417/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982164320849/1000000000000 : ℝ) ≤ (radius 7 (129/1024 : ℝ)) ∧ (radius 7 (129/1024 : ℝ)) ≤ (19643286417/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (129/1024 : ℝ)) (982164320849/1000000000000 : ℝ) (19643286417/20000000000 : ℝ) (7520983643/40000000000 : ℝ) (94012295541/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (129/1024 : ℝ)) (982164320849/1000000000000 : ℝ) (19643286417/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (129/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982164320849/1000000000000 : ℝ) (19643286417/20000000000 : ℝ) (123885270053/125000000000 : ℝ) (39643286417/40000000000 : ℝ) (991042037881/1000000000000 : ℝ) (991042037883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (129/1024 : ℝ)) 1 (123885270053/125000000000 : ℝ) (39643286417/40000000000 : ℝ) (991042037881/1000000000000 : ℝ) (991042037883/1000000000000 : ℝ) (61941381197/62500000000 : ℝ) (495531049577/500000000000 : ℝ) (991062098949/1000000000000 : ℝ) (991062098951/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (129/1024 : ℝ)) 2 (61941381197/62500000000 : ℝ) (495531049577/500000000000 : ℝ) (991062098949/1000000000000 : ℝ) (991062098951/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (129/1024 : ℝ)) 3 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (129/1024 : ℝ)) 4 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (129/1024 : ℝ)) 5 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (129/1024 : ℝ)) 6 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (129/1024 : ℝ)) 7 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (129/1024 : ℝ))) (7520983643/40000000000 : ℝ) (94012295541/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7520983643/40000000000 : ℝ) (94012295541/500000000000 : ℝ) (594012295537/1000000000000 : ℝ) (594012295541/1000000000000 : ℝ) (108404506097/250000000000 : ℝ) (216809012199/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 1 (594012295537/1000000000000 : ℝ) (594012295541/1000000000000 : ℝ) (108404506097/250000000000 : ℝ) (216809012199/500000000000 : ℝ) (256907579981/500000000000 : ℝ) (51381515997/100000000000 : ℝ) (507517918947/1000000000000 : ℝ) (126879479739/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 2 (256907579981/500000000000 : ℝ) (51381515997/100000000000 : ℝ) (507517918947/1000000000000 : ℝ) (126879479739/250000000000 : ℝ) (255333269727/500000000000 : ℝ) (510666539463/1000000000000 : ℝ) (4085254661/8000000000 : ℝ) (102131366527/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 3 (255333269727/500000000000 : ℝ) (510666539463/1000000000000 : ℝ) (4085254661/8000000000 : ℝ) (102131366527/200000000000 : ℝ) (510661686039/1000000000000 : ℝ) (510661686049/1000000000000 : ℝ) (1994772211/3906250000 : ℝ) (255330843013/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 4 (510661686039/1000000000000 : ℝ) (510661686049/1000000000000 : ℝ) (1994772211/3906250000 : ℝ) (255330843013/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 5 (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 6 (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (129/1024 : ℝ))) 7 (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (129/1024 : ℝ)) hmem 8 (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (129/1024 : ℝ))) hcmem 8 (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (129/1024 : ℝ)) (19821241981/20000000000 : ℝ) (991062099053/1000000000000 : ℝ) (510661686027/1000000000000 : ℝ) (255330843019/500000000000 : ℝ) (404689827919/500000000000 : ℝ) (809379655859/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0047_exp_lower
  have heNumeric : (2019090428603/1000000000000 : ℝ)/4 ≤ Real.exp (-10681988031/15625000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019090428603/1000000000000 : ℝ)/4 ≤ Real.exp ((515/4096 : ℝ)-(809379655859/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (515/4096 : ℝ) (129/1024 : ℝ) (809379655859/1000000000000 : ℝ) (2019090428603/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0048; no trusted numerical premise.
theorem cover7_leaf0048_exp_radius : (997748597090714297/1000000000000000000 : ℝ) ≤ Real.exp ((-517/28672 : ℝ)/8) ∧ Real.exp ((-517/28672 : ℝ)/8) ≤ (498874298545357149/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-517/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0048_exp_lower : (459046069658834581/500000000000000000 : ℝ) ≤ Real.exp ((-68366019017/100000000000 : ℝ)/8) ∧ Real.exp ((-68366019017/100000000000 : ℝ)/8) ≤ (918092139317669163/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68366019017/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0048_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009532134531/500000000000 : ℝ) ≤ 4*Real.exp (129/1024 : ℝ)*Real.exp (-mu (radius 7 (517/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009532134531/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (517/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0048_exp_radius
  have hrNumeric : (982130066273/1000000000000 : ℝ) ≤ Real.exp (-517/28672 : ℝ) ∧ Real.exp (-517/28672 : ℝ) ≤ (491065033137/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982130066273/1000000000000 : ℝ) ≤ (radius 7 (517/4096 : ℝ)) ∧ (radius 7 (517/4096 : ℝ)) ≤ (491065033137/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (517/4096 : ℝ)) (982130066273/1000000000000 : ℝ) (491065033137/500000000000 : ℝ) (188203434933/1000000000000 : ℝ) (188203434939/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (517/4096 : ℝ)) (982130066273/1000000000000 : ℝ) (491065033137/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (517/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982130066273/1000000000000 : ℝ) (491065033137/500000000000 : ℝ) (61941564571/62500000000 : ℝ) (991065033137/1000000000000 : ℝ) (99102475563/100000000000 : ℝ) (61939047227/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (517/4096 : ℝ)) 1 (61941564571/62500000000 : ℝ) (991065033137/1000000000000 : ℝ) (99102475563/100000000000 : ℝ) (61939047227/62500000000 : ℝ) (991044894383/1000000000000 : ℝ) (198208978877/200000000000 : ℝ) (495522447089/500000000000 : ℝ) (49552244709/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (517/4096 : ℝ)) 2 (991044894383/1000000000000 : ℝ) (198208978877/200000000000 : ℝ) (495522447089/500000000000 : ℝ) (49552244709/50000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (517/4096 : ℝ)) 3 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (517/4096 : ℝ)) 4 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (517/4096 : ℝ)) 5 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (517/4096 : ℝ)) 6 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (517/4096 : ℝ)) 7 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (517/4096 : ℝ))) (188203434933/1000000000000 : ℝ) (188203434939/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188203434933/1000000000000 : ℝ) (188203434939/1000000000000 : ℝ) (297050858733/500000000000 : ℝ) (59410171747/100000000000 : ℝ) (433824198187/1000000000000 : ℝ) (86764839639/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 1 (297050858733/500000000000 : ℝ) (59410171747/100000000000 : ℝ) (433824198187/1000000000000 : ℝ) (86764839639/200000000000 : ℝ) (256981478913/500000000000 : ℝ) (513962957833/1000000000000 : ℝ) (507676768447/1000000000000 : ℝ) (253838384227/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 2 (256981478913/500000000000 : ℝ) (513962957833/1000000000000 : ℝ) (507676768447/1000000000000 : ℝ) (253838384227/500000000000 : ℝ) (15963120723/31250000000 : ℝ) (63852482893/125000000000 : ℝ) (127702548313/250000000000 : ℝ) (25540509663/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 3 (15963120723/31250000000 : ℝ) (63852482893/125000000000 : ℝ) (127702548313/250000000000 : ℝ) (25540509663/50000000000 : ℝ) (255407514097/500000000000 : ℝ) (255407514101/500000000000 : ℝ) (510815028171/1000000000000 : ℝ) (25540751409/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 4 (255407514097/500000000000 : ℝ) (255407514101/500000000000 : ℝ) (510815028171/1000000000000 : ℝ) (25540751409/50000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 5 (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 6 (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (517/4096 : ℝ))) 7 (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (517/4096 : ℝ)) hmem 8 (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (517/4096 : ℝ))) hcmem 8 (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (517/4096 : ℝ)) (24776122357/25000000000 : ℝ) (991044894283/1000000000000 : ℝ) (255407514091/500000000000 : ℝ) (510815028191/1000000000000 : ℝ) (202409188163/250000000000 : ℝ) (80963675267/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0048_exp_lower
  have heNumeric : (1009532134531/500000000000 : ℝ)/4 ≤ Real.exp (-68366019017/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009532134531/500000000000 : ℝ)/4 ≤ Real.exp ((129/1024 : ℝ)-(80963675267/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (129/1024 : ℝ) (517/4096 : ℝ) (80963675267/100000000000 : ℝ) (1009532134531/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0049; no trusted numerical premise.
theorem cover7_leaf0049_exp_radius : (997744247261516061/1000000000000000000 : ℝ) ≤ Real.exp ((-37/2048 : ℝ)/8) ∧ Real.exp ((-37/2048 : ℝ)/8) ≤ (498872123630758031/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-37/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0049_exp_lower : (918090690767379687/1000000000000000000 : ℝ) ≤ Real.exp ((-136734562489/200000000000 : ℝ)/8) ∧ Real.exp ((-136734562489/200000000000 : ℝ)/8) ≤ (114761336345922461/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136734562489/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0049_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009519392019/500000000000 : ℝ) ≤ 4*Real.exp (517/4096 : ℝ)*Real.exp (-mu (radius 7 (259/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009519392019/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (259/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0049_exp_radius
  have hrNumeric : (245523953223/250000000000 : ℝ) ≤ Real.exp (-37/2048 : ℝ) ∧ Real.exp (-37/2048 : ℝ) ≤ (982095812893/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245523953223/250000000000 : ℝ) ≤ (radius 7 (259/2048 : ℝ)) ∧ (radius 7 (259/2048 : ℝ)) ≤ (982095812893/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (259/2048 : ℝ)) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (259/2048 : ℝ)) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (259/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) (495523953223/500000000000 : ℝ) (991047906447/1000000000000 : ℝ) (991007473681/1000000000000 : ℝ) (495503736841/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (259/2048 : ℝ)) 1 (495523953223/500000000000 : ℝ) (991047906447/1000000000000 : ℝ) (991007473681/1000000000000 : ℝ) (495503736841/500000000000 : ℝ) (991027690063/1000000000000 : ℝ) (198205538013/200000000000 : ℝ) (991027689857/1000000000000 : ℝ) (991027689859/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (259/2048 : ℝ)) 2 (991027690063/1000000000000 : ℝ) (198205538013/200000000000 : ℝ) (991027689857/1000000000000 : ℝ) (991027689859/1000000000000 : ℝ) (24775692249/25000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (259/2048 : ℝ)) 3 (24775692249/25000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (259/2048 : ℝ)) 4 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (259/2048 : ℝ)) 5 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (259/2048 : ℝ)) 6 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (259/2048 : ℝ)) 7 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (259/2048 : ℝ))) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ) (594191048271/1000000000000 : ℝ) (23767641931/40000000000 : ℝ) (4340300641/10000000000 : ℝ) (108507516027/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 1 (594191048271/1000000000000 : ℝ) (23767641931/40000000000 : ℝ) (4340300641/10000000000 : ℝ) (108507516027/250000000000 : ℝ) (102822111237/200000000000 : ℝ) (16065954881/31250000000 : ℝ) (253917692751/500000000000 : ℝ) (50783538551/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 2 (102822111237/200000000000 : ℝ) (16065954881/31250000000 : ℝ) (253917692751/500000000000 : ℝ) (50783538551/100000000000 : ℝ) (510972970843/1000000000000 : ℝ) (510972970851/1000000000000 : ℝ) (127740834429/250000000000 : ℝ) (20438533509/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 3 (510972970843/1000000000000 : ℝ) (510972970851/1000000000000 : ℝ) (127740834429/250000000000 : ℝ) (20438533509/40000000000 : ℝ) (510968154279/1000000000000 : ℝ) (31935509643/62500000000 : ℝ) (31935509641/62500000000 : ℝ) (255484077133/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 4 (510968154279/1000000000000 : ℝ) (31935509643/62500000000 : ℝ) (31935509641/62500000000 : ℝ) (255484077133/500000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 5 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 6 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (259/2048 : ℝ))) 7 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (259/2048 : ℝ)) hmem 8 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (259/2048 : ℝ))) hcmem 8 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (259/2048 : ℝ)) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (809893515551/1000000000000 : ℝ) (80989351557/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0049_exp_lower
  have heNumeric : (1009519392019/500000000000 : ℝ)/4 ≤ Real.exp (-136734562489/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009519392019/500000000000 : ℝ)/4 ≤ Real.exp ((517/4096 : ℝ)-(80989351557/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (517/4096 : ℝ) (259/2048 : ℝ) (80989351557/100000000000 : ℝ) (1009519392019/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0025_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0025_certificate
#check SmaleRate.Proofs.cover7_leaf0026_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0026_certificate
#check SmaleRate.Proofs.cover7_leaf0027_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0027_certificate
#check SmaleRate.Proofs.cover7_leaf0028_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0028_certificate
#check SmaleRate.Proofs.cover7_leaf0029_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0029_certificate
#check SmaleRate.Proofs.cover7_leaf0030_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0030_certificate
#check SmaleRate.Proofs.cover7_leaf0031_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0031_certificate
#check SmaleRate.Proofs.cover7_leaf0032_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0032_certificate
#check SmaleRate.Proofs.cover7_leaf0033_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0033_certificate
#check SmaleRate.Proofs.cover7_leaf0034_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0034_certificate
#check SmaleRate.Proofs.cover7_leaf0035_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0035_certificate
#check SmaleRate.Proofs.cover7_leaf0036_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0036_certificate
#check SmaleRate.Proofs.cover7_leaf0037_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0037_certificate
#check SmaleRate.Proofs.cover7_leaf0038_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0038_certificate
#check SmaleRate.Proofs.cover7_leaf0039_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0039_certificate
#check SmaleRate.Proofs.cover7_leaf0040_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0040_certificate
#check SmaleRate.Proofs.cover7_leaf0041_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0041_certificate
#check SmaleRate.Proofs.cover7_leaf0042_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0042_certificate
#check SmaleRate.Proofs.cover7_leaf0043_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0043_certificate
#check SmaleRate.Proofs.cover7_leaf0044_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0044_certificate
#check SmaleRate.Proofs.cover7_leaf0045_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0045_certificate
#check SmaleRate.Proofs.cover7_leaf0046_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0046_certificate
#check SmaleRate.Proofs.cover7_leaf0047_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0047_certificate
#check SmaleRate.Proofs.cover7_leaf0048_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0048_certificate
#check SmaleRate.Proofs.cover7_leaf0049_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0049_certificate
